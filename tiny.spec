---------------------------------------------
-- Types
---------------------------------------------

type byteT  = bits(8)
type constT = bits(24)
type wordT  = bits(32)
type memT   = wordT -> byteT

construct funcT {fAdd,
                 fAddWithCarry, -- Same as fAdd, but +1 if carry flag set
                 fSub,
                 fCarry, fOverflow, -- Get flags, overflow set by both add and sub

                 -- Multiplication, same as RISC-V (copy them from there?)
                 fLongMul, fLongMulH, fLongHulHSigned,

                 -- Bit operations
                 fAnd, fOr, fXor,

                 -- Cmp
                 fEqual, fLess, fLower,
                 fReserved}

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
   IM :: memT           -- Instruction Memory
   DM :: memT           -- Data Memory, byte-addressed as required by the CakeML compiler,
                        -- and words stored in little-endian format

   CarryFlag :: bool    -- Carry bit, from ALU add
   OverflowFlag :: bool -- Overflow bit, from ALU add and sub

-- Input

   Reset :: bool        -- Reset machine (Input)

-- Output

   OutStrobe :: wordT   -- Output Data (Output)

-- Architecture parameters

   f :: wordT -> wordT  -- Function computed by accelerator
   lastIMAddr :: wordT  -- All IM addresses above this contain zero
   lastDMAddr :: wordT  -- All DM addresses above this contain zero
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
      ret = a + b + [CarryFlag]::bits(32);
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

     case fAnd => a && b
     case fOr  => a || b
     case fXor => a ?? b

     case fEqual => [a == b]
     case fLess => [a < b]
     case fLower => [a <+ b]

     -- TODO
     case fLongMul => 0
     case fLongMulH => 0
     case fLongHulHSigned => 0

     -- NOTE: "Do nothing"
     case fReserved => 0
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

unit incPC () =
   PC <- PC + 4

-- Common functionality
unit norm (func::funcT, wback::bool, strobe::bool, w::regT, a::wordT, b::wordT) = {
   alu = ALU (func, a, b);
   when wback do R(w) <- alu;
   when strobe do OutStrobe <- alu;
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

define LoadConstant (reg::regT, imm::constT) = {
   R(reg) <- SignExtend (imm);
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

define StoreDM (func::funcT, w::regT, a::reg_immT, b::reg_immT) = {
  aV = ri2word (a);
  bV = ri2word (b);

  when bV <=+ lastDMAddr do {
    alignedAddr = bV<31:2> : (0::bits(2));
    DM(alignedAddr) <- aV<7:0>;
    DM(alignedAddr + 1) <- aV<15:8>;
    DM(alignedAddr + 2) <- aV<23:16>;
    DM(alignedAddr + 3) <- aV<31:24>
  };

  norm (func, true, false, w, aV, bV)
}

define StoreDMByte (func::funcT, w::regT, a::reg_immT, b::reg_immT) = {
  aV = ri2word (a);
  bV = ri2word (b);

  when bV <=+ lastDMAddr do
    DM(bV) <- aV<7:0>;

  norm (func, true, false, w, aV, bV)
}

define LoadDM (w::regT, a::reg_immT) = {
  aV = ri2word (a);

  if aV <=+ lastDMAddr then {
    alignedAddr = aV<31:2> : (0::bits(2));
    R(w) <- DM(alignedAddr + 3) : DM(alignedAddr + 2) : DM(alignedAddr + 1) : DM(alignedAddr)
  } else {
    R(w) <- 0
  };

  incPC ()
}

define LoadDMByte (w::regT, a::reg_immT) = {
  aV = ri2word (a);
  if aV <=+ lastDMAddr then
    R(w) <- SignExtend (DM(aV))
  else
    R(w) <- 0;
  incPC ()
}

define Out (func::funcT, w::regT, a::reg_immT, b::reg_immT) =
  norm (func, true, true, w, ri2word (a), ri2word (b))

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

define JumpIfZero (func::funcT, w::reg_immT, a::reg_immT, b::reg_immT) = {
   if ALU (func, ri2word (a), ri2word (b)) == 0 then
     PC <- PC + (ri2word (w))
   else
     incPC ()
}

-- TODO: Redundant? Just flip JumpIfZero branches?
define JumpIfNotZero (func::funcT, w::reg_immT, a::reg_immT, b::reg_immT) = {
   if ALU (func, ri2word (a), ri2word (b)) <> 0 then
     PC <- PC + (ri2word (w))
   else
     incPC ()
}

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

reg_immT DecodeReg_imm (flag::bits(1), v::bits(6)) = {
  if flag == 0 then
    Reg (v)
  else
    Imm (v)
}

instruction Decode (opc::wordT) =
   match opc {
      case 'RIw`1 RIwV 1 const`24' => {
        if RIw == 1 then
          LoadConstant (RIwV, const)
        else
          ReservedInstr
      }

      case 'RIw`1 RIwV 0 RIa`1 RIaV RIb`1 RIbV OpArg Op' => {
        w = DecodeReg_imm (RIw, RIwV);
        a = DecodeReg_imm (RIa, RIaV);
        b = DecodeReg_imm (RIb, RIbV);
        func = [OpArg`4] :: funcT;
        shift = [OpArg`4] :: shiftT;

        match Op {
	  case 9 => JumpIfZero (func, w, a, b)
          case 10 => JumpIfNotZero (func, w, a, b)

          -- Instructions where only RIw = reg makes sense
          case _ => {
            match w {
              case Imm (_) => ReservedInstr
              case Reg (wi) =>
                match Op {
                  case 0 => Normal (func, wi, a, b)
                  case 1 => Shift (shift, wi, a, b)

                  case 2 => StoreDM (func, wi, a, b)
                  case 3 => StoreDMByte (func, wi, a, b)
                  case 4 => LoadDM (wi, a)
                  case 5 => LoadDMByte (wi, a)
                  case 6 => Out (func, wi, a, b)
                  case 7 => Accelerator (wi, a)

                  case 8 => Jump (func, wi, a)

                  case _ => ReservedInstr
                }
              }
            }
          }
        }
      }

---------------------------------------------
-- Next State
---------------------------------------------

unit Next = {
   if Reset then {
      PC <- 0
   } else {
      when PC <=+ lastIMAddr do {
        alignedAddr = PC<31:2> : (0::bits(2));
        i = Decode (IM (PC + 3) : IM (PC + 2) : IM (PC + 1) : IM (PC));
        -- NOTE: "Do nothing" if unknown instruction
        when i <> ReservedInstr do Run (i)
      }
   }
}

---------------------------------------------
-- Encode
---------------------------------------------

bits(7) ri2bits (ri::reg_immT) =
  match ri {
    case Reg (i) => 0::bits(1) : i
    case Imm (v) => 1::bits(1) : v
  }

wordT enc (func::funcT, w::reg_immT, a::reg_immT, b::reg_immT, opc::bits(6)) = {
   return (ri2bits (w) : '0' : ri2bits (a) : ri2bits (b) : [func]`4 : opc)
}

wordT encShift (shift::shiftT, w::reg_immT, a::reg_immT, b::reg_immT, opc::bits(6)) = {
   return (ri2bits (w) : '0' : ri2bits (a) : ri2bits (b) : [shift]`4 : opc)
}

wordT Encode (i::instruction) =
   match i {
      case LoadConstant (Rw, const) => '0' : Rw : '1' : const

      case Normal (func, w, a, b) => enc (func, Reg (w), a, b, '000000')
      case Shift (shift, w, a, b) => encShift (shift, Reg (w), a, b, '000001')

      case StoreDM (func, w, a, b) => enc (func, Reg (w), a, b, '000010')
      case StoreDMByte (func, w, a, b) => enc (func, Reg (w), a, b, '000011')
      case LoadDM (w, a) => enc (fReserved, Reg (w), a, Imm (0), '000100')
      case LoadDMByte (w, a) => enc (fReserved, Reg (w), a, Imm (0), '000101')
      case Out (func, w, a, b) => enc (func, Reg (w), a, b, '000110')
      case Accelerator (w, a) => enc (fReserved, Reg (w), a, Imm (0), '000111')

      case Jump (func, w, a) => enc (func, Reg (w), a, Imm (0), '001000')
      case JumpIfZero (func, w, a, b) => enc (func, w, a, b, '001001')
      case JumpIfNotZero (func, w, a, b) => enc (func, w, a, b, '001010')
      case _ => 0b111111
   }

---------------------------------------------
-- Load into Instruction Memory
---------------------------------------------

--unit LoadIM (a::wordT, i::instruction list) measure Length (i) =
--   match i
--   {
--      case Nil => nothing
--      case h @ t =>
--        {
--           IM(a) <- Encode (h);
--           LoadIM (a + 1, t)
--        }
--   }

---------------------------------------------
-- Initialization & testing
---------------------------------------------

--unit initialize (p::instruction list) =
--{
--   Reset <- false;
--   PC <- 0;
--   R <- InitMap (0);
--   DM <- InitMap (0);
---- InRdy <- false;
---- InData <- 0;
--   OutStrobe <- 0;
--   IM <- InitMap (Encode (ReservedInstr));
--   LoadIM (0, p)
--}

--instruction list test_prog =
--   list {
--      LoadConstant (0, 0),
--      LoadConstant (1, 1000),
--      LoadConstant (2, 1010),
--      LoadConstant (3, 4),
--      StoreDM (fINC, noShift, skipNever, 1, 1, 1),
--      Normal (fXOR, noShift, skipZero, 4, 1, 2),
--      Jump (fADD, noShift, 4, 3, 0),
--      Out (fADD, noShift, skipNever, 1, 1, 0)
--   }
