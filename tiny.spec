---------------------------------------------
-- Types
---------------------------------------------

type byteT  = bits(8)
type wordT  = bits(32)
type memT   = wordT -> byteT

construct funcT {
  fAdd,
  fAddWithCarry, -- Same as fAdd, but +1 if carry flag set
  fSub,
  fCarry, fOverflow, -- Get flags, overflow set by both add and sub

  fInc, fDec, -- Add and subtract by 1

  -- Multiplication, same as RISC-V's MUL and MULHU
  fMul, fMulHU,

  -- Bit operations
  fAnd, fOr, fXor,

  -- Cmp
  fEqual, fLess, fLower,

  -- Snd
  fSnd
}

construct shiftT {shiftLL, shiftLR, shiftAR, shiftRor, shiftReserved}

type regT = bits(6)
type immT = bits(6)
-- Imm if bit above set, reg otherwise
construct reg_immT {Reg :: regT, Imm :: immT}

---------------------------------------------
-- State
---------------------------------------------

declare {
-- State

   PC :: wordT          -- Program Counter
   R :: regT -> wordT   -- Registers
   MEM :: memT          -- Main Memory, byte-addressed as required by the
                        -- CakeML compiler, and words stored in little-endian
                        -- format

   CarryFlag :: bool    -- Carry bit, from ALU add
   OverflowFlag :: bool -- Overflow bit, from ALU add and sub

-- IO

   data_out :: bits(16) -- Output Data (Output)
   data_in  :: bits(16) -- Output Data (Input)

-- Architecture parameters

   f :: wordT -> wordT  -- Function computed by accelerator
   lastMemAddr :: wordT -- All MEM addresses above this contain zero
}

---------------------------------------------
-- Operations
---------------------------------------------

wordT ALU (func::funcT, a::wordT, b::wordT) =
   match func {
     case fAdd => {
       ret = a + b;
       CarryFlag <- 0n2**0n32 <= [a]::nat + [b]::nat;
       OverflowFlag <- [ret]::int <> [a]::int + [b]::int;
       ret
     }
     case fAddWithCarry => {
      ret = a + b + [CarryFlag]`32;
      CarryFlag <- 0n2**0n32 <= [a]::nat + [b]::nat + [CarryFlag]::nat;
      OverflowFlag <- [ret]::int <> [a]::int + [b]::int + [CarryFlag]::int;
      ret
     }
     case fSub => {
       ret = a - b;
       OverflowFlag <- [ret]::int <> [a]::int - [b]::int;
       ret
     }

     case fCarry => [CarryFlag]
     case fOverflow => [OverflowFlag]

     case fInc => a + 1
     case fDec => a - 1

     case fMul => a * b
     case fMulHU => {
       prod`64 = ZeroExtend (a) * ZeroExtend (b);
       prod<63:32>
     }

     case fAnd => a && b
     case fOr  => a || b
     case fXor => a ?? b

     case fEqual => [a == b]
     case fLess => [a < b]
     case fLower => [a <+ b]

     case fSnd => b
   }

wordT shift (shiftOp::shiftT, a::wordT, b::wordT) =
   match shiftOp {
     case shiftLL => a << b
     case shiftLR => a >>+ b
     case shiftAR => a >> b
     case shiftRor => a #>> b
     -- NOTE: "Do nothing"
     case shiftReserved => 0
   }

unit incPC () = PC <- PC + 4

-- Common functionality
unit norm (func::funcT, wback::bool, out::bool, w::regT, a::wordT, b::wordT) = {
   alu = ALU (func, a, b);
   when wback do R(w) <- alu;
   when out do data_out <- [alu];
   incPC ()
}

wordT ri2word (ri::reg_immT) =
  match ri {
    case Reg (i) => R (i)
    case Imm (v) => SignExtend (v)
  }

---------------------------------------------
-- Instructions
---------------------------------------------

define LoadUpperConstant (reg::regT, imm::bits(9)) = {
   R(reg)<31:23> <- imm;
   incPC ()
}

define LoadConstant (reg::regT, negate::bool, imm::bits(23)) = {
   v = ZeroExtend (imm);
   R(reg) <- if negate then -v else v;
   incPC ()
}

define Normal (func::funcT, w::regT, a::reg_immT, b::reg_immT) =
  norm (func, true, false, w, ri2word (a), ri2word (b))

define Shift (shiftOp::shiftT, w::regT, a::reg_immT, b::reg_immT) = {
  R(w) <- shift (shiftOp, ri2word (a), ri2word (b));
  incPC ()
}

-- All bytes must be addressable, but this is only relevant for byte IO; because
-- word IO addresses must be word-aliged, and non-aliged addresses are rounded down
-- to the closest aligned address.

define StoreMEM (func::funcT, w::regT, a::reg_immT, b::reg_immT) = {
  aV = ri2word (a);
  bV = ri2word (b);

  when bV <+ lastMemAddr do {
    alignedAddr = bV<31:2> : 0`2;
    MEM(alignedAddr) <- aV<7:0>;
    MEM(alignedAddr + 1) <- aV<15:8>;
    MEM(alignedAddr + 2) <- aV<23:16>;
    MEM(alignedAddr + 3) <- aV<31:24>
  };

  norm (func, true, false, w, bV, bV)
}

define StoreMEMByte (func::funcT, w::regT, a::reg_immT, b::reg_immT) = {
  aV = ri2word (a);
  bV = ri2word (b);

  when bV <+ lastMemAddr do
    MEM(bV) <- aV<7:0>;

  norm (func, true, false, w, bV, bV)
}

define LoadMEM (w::regT, a::reg_immT) = {
  aV = ri2word (a);

  if aV <+ lastMemAddr then {
    alignedAddr = aV<31:2> : 0`2;
    R(w) <- MEM(alignedAddr + 3) : MEM(alignedAddr + 2) :
            MEM(alignedAddr + 1) : MEM(alignedAddr)
  } else
    R(w) <- 0;

  incPC ()
}

define LoadMEMByte (w::regT, a::reg_immT) = {
  aV = ri2word (a);
  if aV <+ lastMemAddr then
    R(w) <- ZeroExtend (MEM(aV))
  else
    R(w) <- 0;
  incPC ()
}

define Out (func::funcT, w::regT, a::reg_immT, b::reg_immT) =
  norm (func, true, true, w, ri2word (a), ri2word (b))

define In (w::regT) = {
   R(w) <- ZeroExtend (data_in);
   incPC ()
}

define Accelerator (w::regT, a::reg_immT) = {
   -- This is fairly limited, might want to send both a and b.
   -- An even more advanced/flexible interface would send multiple bytes from memory or similar,
   -- or allow the accelerator to access memory directly.
   R(w) <- f (ri2word (a));
   incPC ()
}

define Jump (func::funcT, w::regT, a::reg_immT) = {
   PC1 = PC + 4;
   PC <- ALU (func, PC, ri2word (a));
   R(w) <- PC1
}

define JumpIfZero (func::funcT, w::reg_immT, a::reg_immT, b::reg_immT) =
   if ALU (func, ri2word (a), ri2word (b)) == 0 then
     PC <- PC + ri2word (w)
   else
     incPC ()

-- TODO: Redundant? Just flip JumpIfZero branches?
define JumpIfNotZero (func::funcT, w::reg_immT, a::reg_immT, b::reg_immT) =
   if ALU (func, ri2word (a), ri2word (b)) <> 0 then
     PC <- PC + ri2word (w)
   else
     incPC ()

-- Do nothing, do not want the original definition:
--
--   define ReservedInstr = #Reserved
--
-- Because we do not want exceptions...
define ReservedInstr = nothing

define Run

---------------------------------------------
-- Decode
---------------------------------------------

reg_immT DecodeReg_imm (flag::bits(1), v::bits(6)) =
  if flag == 0 then
    Reg (v)
  else
    Imm (v)

instruction Decode (opc::wordT) =
   match opc {

      case '0 RIwV 1 0`15 const`9' => LoadUpperConstant (RIwV, const)
      case '1 RIwV 1 neg`1 const`23' => LoadConstant (RIwV, [neg], const)
      case '_`7 1 _`24' => ReservedInstr

      case 'RIw`1 RIwV 0 RIa`1 RIaV RIb`1 RIbV OpArg Op' => {
        w = DecodeReg_imm (RIw, RIwV);
        a = DecodeReg_imm (RIa, RIaV);
        b = DecodeReg_imm (RIb, RIbV);
        func = [OpArg`4] :: funcT;
        shift = [OpArg`4] :: shiftT;

        match Op {
          case 10 => JumpIfZero (func, w, a, b)
          case 11 => JumpIfNotZero (func, w, a, b)

          -- Instructions where only RIw = reg makes sense
          case _ =>
            match w {
              case Imm (_) => ReservedInstr
              case Reg (wi) =>
                match Op {
                  case 0 => Normal (func, wi, a, b)
                  case 1 => Shift (shift, wi, a, b)

                  case 2 => StoreMEM (func, wi, a, b)
                  case 3 => StoreMEMByte (func, wi, a, b)
                  case 4 => LoadMEM (wi, a)
                  case 5 => LoadMEMByte (wi, a)
                  case 6 => Out (func, wi, a, b)
                  case 7 => In (wi)
                  case 8 => Accelerator (wi, a)

                  case 9 => Jump (func, wi, a)

                  case _ => ReservedInstr
                }
            }
        }
      }
   }

---------------------------------------------
-- Next State
---------------------------------------------

unit Next =
  when PC <+ lastMemAddr do {
    alignedAddr = PC<31:2> : 0`2;
    Run (Decode (MEM (alignedAddr + 3) : MEM (alignedAddr + 2) :
                 MEM (alignedAddr + 1) : MEM (alignedAddr)))
  }

---------------------------------------------
-- Encode
---------------------------------------------

bits(7) ri2bits (ri::reg_immT) =
  match ri {
    case Reg (i) => 0 : i
    case Imm (v) => 1 : v
  }

wordT enc (func::funcT, w::reg_immT, a::reg_immT, b::reg_immT, opc::bits(6)) =
   ri2bits (w) : '0' : ri2bits (a) : ri2bits (b) : [func]`4 : opc

wordT encShift (shift::shiftT, w::reg_immT, a::reg_immT, b::reg_immT, opc::bits(6)) =
   ri2bits (w) : '0' : ri2bits (a) : ri2bits (b) : [shift]`4 : opc

wordT Encode (i::instruction) =
   match i {
      case LoadUpperConstant (Rw, const) => '0' : Rw : '1' : 0`15 : const
      case LoadConstant (Rw, neg, const) => '1' : Rw : '1' : [neg] : const

      case Normal (func, w, a, b) => enc (func, Reg (w), a, b, '000000')
      case Shift (shift, w, a, b) => encShift (shift, Reg (w), a, b, '000001')

      case StoreMEM (func, w, a, b) => enc (func, Reg (w), a, b, '000010')
      case StoreMEMByte (func, w, a, b) => enc (func, Reg (w), a, b, '000011')
      case LoadMEM (w, a) => enc (fAdd, Reg (w), a, Imm (0), '000100')
      case LoadMEMByte (w, a) => enc (fAdd, Reg (w), a, Imm (0), '000101')
      case Out (func, w, a, b) => enc (func, Reg (w), a, b, '000110')
      case In (w) => enc (fAdd, Reg (w), Imm (0), Imm (0), '000111')
      case Accelerator (w, a) => enc (fAdd, Reg (w), a, Imm (0), '001000')

      case Jump (func, w, a) => enc (func, Reg (w), a, Imm (0), '001001')
      case JumpIfZero (func, w, a, b) => enc (func, w, a, b, '001010')
      case JumpIfNotZero (func, w, a, b) => enc (func, w, a, b, '001011')
      case _ => 0b111111
   }

{-----------------------------------------------------------------------------

---------------------------------------------
-- Load into Instruction Memory
---------------------------------------------

unit LoadMEM (a::wordT, i::instruction list) measure Length (i) =
   match i
   {
      case Nil => nothing
      case h @ t =>
        {
           'b1 b2 b3 b4' = Encode (h);
           MEM(a)   <- b4;
           MEM(a+1) <- b3;
           MEM(a+2) <- b2;
           MEM(a+3) <- b1;
           LoadMEM (a + 4, t)
        }
   }

---------------------------------------------
-- Initialization & testing
---------------------------------------------

unit initialize (p::instruction list) =
{
-- Reset <- false;
   PC <- 0;
   R <- InitMap (0);
   MEM <- InitMap (0);
-- InRdy <- false;
   data_in <- 0;
   data_out <- 0;
   LoadMEM (0, p)
}

-----------------------------------------------------------------------------}
