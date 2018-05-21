---------------------------------------------
-- Types
---------------------------------------------

type regT  = bits(6)
type wordT = bits(32)
type immT  = bits(24)
type addrT = bits(10)
type OpArgT = bits(4)
type memT  = addrT -> wordT

--type funcT = bits(3)
--type shiftT = bits(2)
--type conditionT = bits(2)

---------------------------------------------
-- State
---------------------------------------------

declare
{
   --
   -- Memory interface
   --

   -- Memory state
   mem_fun :: memT

   -- Port A (data)
   mem_inst_addr :: addrT
   mem_inst_out :: wordT

   -- Port B (instruction)
   mem_data_addr :: addrT
   mem_data_mask :: bits(4)
   mem_data_in :: wordT
   mem_data_out :: wordT

   lastMemAddr :: wordT -- All MEM addresses above this contain zero,
                        -- and cannot be written to

   ---
   --- Processor
   ---

   -- Internal/implementation state
   state :: bits(2)
   -- TODO: Can probably use just addrT here, and pad with zero bits in the simulation relation,
   -- TODO: but this is simpler for now
   PC :: wordT          -- Program Counter
   R :: regT -> wordT   -- Registers

   CarryFlag :: bool    -- Carry bit, from ALU add
   OverflowFlag :: bool -- Overflow bit, from ALU add and sub
   ALU_res :: wordT     -- "Inlining" variable, from inlining ALU function

   instruction :: bits(4) -- "Inlining" variable

   -- Data memory internal control
   -- Write delayed in the sense that the write to a register is delayed
   delay_write :: regT
   -- 0 = lowest byte
   -- 1 = second lowest byte
   -- 2 = second highest byte
   -- 3 = highest byte
   -- 4 = all bytes
   -- 5 = no write
   do_delay_write :: bits(3)

   -- Inputs and outputs
   data_out :: bits(16) -- Output data (16 bits because that's how many LEDs we have on the FPGA board)
   data_in :: bits(16)  -- Input data

   -- If we could read from comm vars this wouldn't be needed...
   first_wait_acc_cycle :: bool

   --
   -- Accelerator<->processor communication
   --
   acc_arg :: wordT
   acc_arg_ready :: bool
   acc_res :: wordT
   acc_res_ready :: bool

   acc_state :: bits(2)
}

---------------------------------------------
-- Operations
---------------------------------------------

-- Run is a reserved name
unit ImplRun (i::wordT) = {
  --
  -- Decode instruction
  --

  if i<24> then {
    -- Load constants

    if i<31> then
      instruction <- 12 -- LoadConstant
    else if i<23:9> == 0 then
      instruction <- 13 -- LoadUpperConstant
    else
      instruction <- 15 -- Invalid instruction
  } else {
    if (i<5:0> == 10 or i<5:0> == 11) then {
      instruction <- i<3:0>
    } else if i<31> then {
      instruction <- 15
    } else {
      if (i<5:0> <+ 10) then
        instruction <- i<3:0>
      else
        instruction <- 15
    }
  };

  --
  -- Decode registers: Reg/imm a and b as values (this does ri2word)
  --
  wV = if i<31> then (SignExtend (i<30:25>)) else R(i<30:25>);
  aV = if i<23> then (SignExtend (i<22:17>)) else R(i<22:17>);
  bV = if i<16> then (SignExtend (i<15:10>)) else R(i<15:10>);

  mem_byte_pattern = 1 << (ZeroExtend (bV<1:0>) :: bits(4));

  --
  -- Connect parts (experiment to make correctness proofs easier initially)
  --
  --disable_func = (instruction == 11) or
  --               (instruction == 12) or
  --               (instruction == 1) or
  --               (instruction == 4) or
  --	         (instruction == 5) or
  --	         (instruction == 7) or
  --	         (instruction == 15);

  --func = if disable_func then 3 else i<9:6>;
  func = i<9:6>;

--
-- ALU inline end
--
   ALU_fst = (if instruction == 9 then PC else aV);
   ALU_snd = (if instruction == 9 then aV else bV);

   ALU_prod = ZeroExtend (ALU_fst) * ZeroExtend (ALU_snd) :: bits(65);
   ALU_sum = ZeroExtend (ALU_fst) +
             ZeroExtend (ALU_snd) +
             (if (func == 1) then [CarryFlag] else 0) :: bits(33);

   -- NOTE: Signs must be equal after if they are equal before
   -- TODO: Implication operator does not work in L3 for some reason?
   ALU_OverflowFlag = (ALU_fst<31> == ALU_snd<31>) and (ALU_sum<31> != ALU_fst<31>);

   match func {
     case 0 => { -- fAdd
       ALU_res <- ALU_sum<31:0>;
       CarryFlag <- ALU_sum<32>;
       OverflowFlag <- ALU_OverflowFlag
     }
     case 1 => { -- fAddWithCarry
       ALU_res <- ALU_sum<31:0>;
       CarryFlag <- ALU_sum<32>;
       OverflowFlag <- ALU_OverflowFlag
     }
     case 2 => { -- fSub
       -- Similar to ALU_OverflowFlag, but b inverted
       ALU_sub = ZeroExtend (ALU_fst) - ZeroExtend (ALU_snd) :: bits(33);
       OverflowFlag <- (ALU_fst<31> != ALU_snd<31>) and (ALU_sub<31> != ALU_fst<31>);
       ALU_res <- ALU_sub<31:0>
     }

     case 3 => ALU_res <- [CarryFlag]
     case 4 => ALU_res <- [OverflowFlag]

     case 5 => ALU_res <- ALU_fst + 1
     case 6 => ALU_res <- ALU_fst - 1

     case 7 => ALU_res <- ALU_prod<31:0>
     case 8 => ALU_res <- ALU_prod<63:32>

     case 9 => ALU_res <- ALU_fst && ALU_snd
     case 10 => ALU_res <- ALU_fst || ALU_snd
     case 11 => ALU_res <- ALU_fst ?? ALU_snd

     case 12 => ALU_res <- [ALU_fst == ALU_snd]
     case 13 => ALU_res <- [ALU_fst < ALU_snd]
     case 14 => ALU_res <- [ALU_fst <+ ALU_snd]

     case 15 => ALU_res <- ALU_snd
   };

--
-- ALU inline end
--

  incPC = PC + 4;

  --
  -- Execute instruction
  --

  match instruction {
  case 0 => { -- Normal
    R(i<30:25>) <- ALU_res;
    PC <- incPC;
    state <- 1
  }

  case 1 => { -- Shift
    -- DIFF: shift inlined, could maybe have a CONV that pushes the assignment automatically?
    -- TODO: Disabled for how, translation does not handled shifts
    --match i<9:6> {
    --  case 0 => R(i<30:25>) <- aV << bV
    --  case 1 => R(i<30:25>) <- aV >>+ bV
    --  case 2 => R(i<30:25>) <- aV >> bV
    --  case 3 => R(i<30:25>) <- aV #>> bV
    --  case _ => nothing
    --};
    PC <- incPC;
    state <- 1
  }

  case 2 => { -- StoreMEM
    when bV <+ lastMemAddr do {
      mem_data_addr <- bV<11:2>;
      mem_data_in <- aV;
      mem_data_mask <- 15 -- NOTE: all 4 bits high
    };

    R(i<30:25>) <- ALU_res;
    PC <- incPC;
    state <- 1
  }

  case 3 => { -- StoreMEMByte
    when bV <+ lastMemAddr do {
      mem_data_addr <- bV<11:2>;

      -- TODO: Less stupid way of doing this?
      match bV<1:0> {
        case 0 => mem_data_in<7:0> <- aV<7:0>
        case 1 => mem_data_in<15:8> <- aV<7:0>
        case 2 => mem_data_in<23:16> <- aV<7:0>
        case 3 => mem_data_in<31:24> <- aV<7:0>
      };

      mem_data_mask <- mem_byte_pattern
    };

    R(i<30:25>) <- ALU_res;
    PC <- incPC;
    state <- 1
  }

  case 4 => { -- LoadMEM
    if aV <+ lastMemAddr then {
      delay_write <- i<30:25>;
      do_delay_write <- 4;
      mem_data_addr <- aV<11:2>
    } else {
      R(i<30:25>) <- 0
    };

    PC <- incPC;
    state <- 1
  }

  case 5 => { -- LoadMEMByte
    if aV <+ lastMemAddr then {
      delay_write <- i<30:25>;
      do_delay_write <- ZeroExtend (bV<1:0>);
      mem_data_addr <- aV<11:2>
    } else {
      R(i<30:25>) <- 0
    };

    PC <- incPC;
    state <- 1
  }

  case 6 => { -- Out
    R(i<30:25>) <- ALU_res;
    data_out <- ALU_res<15:0>;
    PC <- incPC;
    state <- 1
  }

  case 7 => { -- In
    R(i<30:25>) <- ZeroExtend (data_in);
    PC <- incPC;
    state <- 1
  }

  case 8 => { -- Accelerator
    delay_write <- i<30:25>;
    acc_arg <- aV;
    acc_arg_ready <- true;
    first_wait_acc_cycle <- true;
    PC <- incPC;
    state <- 3
  }

  case 9 => { -- Jump
    R(i<30:25>) <- PC + 1;
    PC <- ALU_res;
    state <- 1
  }

  case 10 => { -- JumpIfZero
    if ALU_res == 0 then {
      PC <- PC + wV
    } else {
      PC <- incPC
    };

    state <- 1
  }

  case 11 => { -- JumpIfNotZero
    if ALU_res <> 0 then {
      PC <- PC + wV
    } else {
      PC <- incPC
    };

    state <- 1
  }

  case 12 => { -- LoadConstant, TODO: can reuse ALU here
    if i<23> then
      R(i<30:25>) <- 0 - ZeroExtend (i<22:0>)
    else
      R(i<30:25>) <- ZeroExtend (i<22:0>);

    PC <- incPC;
    state <- 1
  }

  case 13 => { -- LoadUpperConstant
    R(i<30:25>)<31:23> <- i<8:0>;
    PC <- incPC;
    state <- 1
  }

  case _ => nothing
  }
}

---------------------------------------------
-- Next State
---------------------------------------------

unit Next =
{
  -- I.e., lastMemAddr from spec is 2^10 - 1 (= 2^|addrT| - 1)
  match state {
    -- cpu_do
    case 0 => {
      when PC <+ lastMemAddr do {
        ImplRun (mem_inst_out)
      }
    }

    -- cpu_read (should be named: cpu_wait_for_inst_read)
    case 1 => {
      mem_data_mask <- 0;

      if do_delay_write == 5 then {
        state <- 0
      } else {
        -- We are going to read from data mem
        state <- 2
      }
    }

    -- cpu_wait_for_data_read
    case 2 => {
      match do_delay_write {
        case 0 => R(delay_write) <- ZeroExtend (mem_data_out<7:0>)
        case 1 => R(delay_write) <- ZeroExtend (mem_data_out<15:8>)
        case 2 => R(delay_write) <- ZeroExtend (mem_data_out<23:16>)
        case 3 => R(delay_write) <- ZeroExtend (mem_data_out<31:24>)
        case 4 => R(delay_write) <- mem_data_out
        case _ => nothing
      };

      do_delay_write <- 5;
      state <- 0
    }

    -- cpu_wait_for_acc
    case 3 => {
      if first_wait_acc_cycle then {
        acc_arg_ready <- false;
	first_wait_acc_cycle <- false
      } else {
        when acc_res_ready do {
          R(delay_write) <- acc_res;
          state <- 0
        }
      }
    }

    -- Cannot happen
    --case _ => {
    --  state <- 0
    --}
  };

  -- Instruction address translation
  mem_inst_addr <- PC<11:2>
}

---------------------------------------------
-- Memory
---------------------------------------------

unit mem_Next =
{
   -- In the spec we do inst reads / data writes in this order, so
   -- the order must be the same here.

   -- See e.g. http://www.cs.columbia.edu/~sedwards/classes/2015/4840/memory.pdf#page=40
   -- Both writes should be non-blocking, and order is important here (return old value)

   mem_inst_out <- mem_fun(mem_inst_addr);
   mem_data_out <- mem_fun(mem_data_addr);

   -- TODO: Could use for loop here, but would have to do EVAL or other simplification
   -- TODO: to remove arithmetic probably...
   when mem_data_mask<0> do {
     mem_fun(mem_data_addr)<7:0> <- mem_data_in<7:0>
   };

   when mem_data_mask<1> do {
     mem_fun(mem_data_addr)<15:8> <- mem_data_in<15:8>
   };

   when mem_data_mask<2> do {
     mem_fun(mem_data_addr)<23:16> <- mem_data_in<23:16>
   };

   when mem_data_mask<3> do {
     mem_fun(mem_data_addr)<31:24> <- mem_data_in<31:24>
   }
}

---------------------------------------------
-- Accelerator, simple examples with plus
---------------------------------------------

unit acc_Next =
{
  match acc_state {
    case 0 => {
      when (acc_arg_ready) do {
        acc_state <- 1
      }
    }

    case 1 => {
      acc_state <- 2
    }

    case 2 => {
      acc_res <- ZeroExtend (acc_arg<31:16> + acc_arg<15:0>);
      acc_res_ready <- true;
      acc_state <- 3
    }

    case 3 => {
      acc_res_ready <- false;
      acc_state <- 0
    }
  }
}
