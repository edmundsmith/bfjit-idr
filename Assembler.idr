module Assembler

import Effects
import Effect.State
import Effect.File
import Effect.StdIO
import Effect.Exception
import Data.Bits

%access public export

data Reg : Type where
	RAX : Reg		-- Accumulator
	RCX : Reg		-- Counter
	RDX : Reg		-- Data
	RBX : Reg		-- General purpose
	RSP : Reg		-- Stack pointer
	RBP : Reg		-- Previous stack frame
	RSI : Reg		-- Source index
	RDI : Reg		-- Destination index

Show Reg where
	show RAX = "RAX"
	show RCX = "RCX"
	show RDX = "RDX"
	show RBX = "RBX"
	show RSP = "RSP"
	show RBP = "RBP"
	show RSI = "RSI"
	show RDI = "RDI"

Eq Reg where
	RAX == RAX = True
	RCX == RCX = True
	RDX == RDX = True
	RBX == RBX = True
	RSP == RSP = True
	RBP == RBP = True
	RSI == RSI = True
	RDI == RDI = True
	_ == _ = False

index : Reg -> Bits8
index RAX = 0
index RCX = 1
index RDX = 2
index RBX = 3
index RSP = 4
index RBP = 5
index RSI = 6
index RDI = 7

data Val : Type where
	I : Bits64 -> Val
	R : Reg -> Val
	A : Bits32 -> Val

Show Val where
	show (I lit) = "I " ++ show lit
	show (R reg) = "R " ++ show reg
	show (A addr)= "A " ++ show addr

Eq Val where
	(I x) == (I y) = x == y
	(R x) == (R y) = x == y
	(A x) == (A y) = x == y
	_ == _ = False

data Instr : Type where
	Ret : Instr
	Move : Val -> Val -> Instr
	Add : Val -> Val -> Instr
	Sub : Val -> Val -> Instr
	Mul : Val -> Instr
	IMul : Val -> Val -> Instr
	Xor : Val -> Val -> Instr
	Inc : Val -> Instr
	Dec : Val -> Instr
	Push : Val -> Instr
	Pop : Val -> Instr
	Call : Val -> Instr
	Loop : Val -> Instr
	Nop : Instr
	Syscall : Instr

Show Instr where
	show Ret = "Ret"
	show (Move x y) = "Move " ++ show x ++ " " ++ show y
	show (Add x y) = "Add " ++ show x ++ " " ++ show y
	show (Sub x y) = "Sub " ++ show x ++ " " ++ show y
	show (Mul x) = "Mul " ++ show x
	show (IMul x y) = "IMul " ++ show x ++ " " ++ show y
	show (Xor x y) = "Xor " ++ show x ++ " " ++ show y
	show (Inc x) = "Inc " ++ show x
	show (Dec x) = "Dec " ++ show x
	show (Push x) = "Push " ++ show x
	show (Pop x) = "Pop " ++ show x
	show (Call x) = "Call " ++ show x
	show (Loop x) = "Loop " ++ show x
	show Nop = "Nop"
	show Syscall = "Syscall"

Eq Instr where
	(==) Ret Ret = True
	(==) (Move x1 y1) (Move x2 y2) = x1 == x2 && y1 == y2
	(==) (Add x1 y1) (Add x2 y2) = x1 == x2 && y1 == y2
	(==) (Sub x1 y1) (Sub x2 y2) = x1 == x2 && y1 == y2
	(==) (Mul x1) (Mul x2) = x1 == x2
	(==) (IMul x1 y1) (IMul x2 y2) = x1 == x2 && y1 == y2
	(==) (Xor x1 y1) (Xor x2 y2) = x1 == x2 && y1 == y2
	(==) (Inc x1) (Inc x2) = x1 == x2
	(==) (Dec x1) (Dec x2) = x1 == x2
	(==) (Push x1) (Push x2) = x1 == x2
	(==) (Pop x1) (Pop x2) = x1 == x2
	(==) (Call x1) (Call x2) = x1 == x2
	(==) (Loop x1) (Loop x2) = x1 == x2
	(==) (Nop) (Nop) = True
	(==) (Syscall) (Syscall) = True
	(==) _ _ = False

record JITMem where
	constructor MkJIT
	instrs : List Instr
	mach : List Bits8
	icount : Bits32
	memptr : Bits64
	memoff : Bits64

Show JITMem where
	show jit = "JIT {" ++ 
		" Instrs: " ++ show (instrs jit) ++ 
		" Mach: " ++ show (mach jit) ++
		" Count: " ++ show (icount jit) ++ 
		" at " ++ show  (memptr jit) ++ 
		"+" ++ show (memoff jit) ++ "}"

Neg Bits32 where
	(-) = prim__subB32
	negate x = 0 - x
	abs x = x


efflist : List EFFECT
efflist = ['jit ::: STATE JITMem, --'
			EXCEPTION String]

X86 : Type -> Type
X86 a = Effects.SimpleEff.Eff a efflist

--DEJA VU! I'VE JUST BEEN THIS PLACE BEFORE
initialJIT : Bits64 -> JITMem
initialJIT startPtr = MkJIT [] [] 0 startPtr startPtr

appendBits : List Bits8 -> JITMem -> JITMem
appendBits bits = record {mach $= (++ bits), memoff $= (+ (natToBits {n=3} (length bits))) }

orBits8 : Bits8 -> Bits8 -> Bits8
orBits8 = prim__orB8

rax : Val
rax = R RAX
rbx : Val
rbx = R RBX
rcx : Val
rcx = R RCX
rdx : Val
rdx = R RDX
rsp : Val
rsp = R RSP
rbp : Val
rbp = R RBP
rsi : Val
rsi = R RSI
rdi : Val
rdi = R RDI


emit : List Bits8 -> X86 ()
emit bits = 'jit :- update (appendBits bits) --' Sublime doesn't like single apostophes

imm : Bits64 -> X86 ()
imm val = emit $ reverse $ b64ToBytes val

imm32 : Bits32 -> X86 ()
imm32 val = emit $ reverse $ b32ToBytes val

ret : X86 ()
ret = do emit [0xC3]

nop : X86 ()
nop = do emit [0x90]

syscall : X86 ()
syscall = do
	emit [0x0f]
	emit [0x05]


add : Val -> Val -> X86 ()
add (R l) (I r) = do
	emit [0x48]
	emit [0x05]
	imm r
add (R l) (R r) = do
	emit [0x48]
	emit [0x01]
	emit [(0xc0 `orBits8` (shiftLeft' {n=1} (index r) 3)) `orBits8` (index l)]
add l r = do 
	raise {b=()} $ "Cannot add " ++ show l ++ " to " ++ show r
	pure ()

sub : Val -> Val -> X86 ()
sub (R l) (I r) = do
	emit [0x48]
	emit [0x2D]
	imm r
sub (R l) (R r) = do
	emit [0x48]
	emit [0x29]
	emit [(0xc0 `orBits8` (shiftLeft' {n=1} (index r) 3)) `orBits8` (index l)]
sub l r = do
	raise {b=()} $ "Cannot sub " ++ show r ++ " from " ++ show l
	pure ()

push : Val -> X86 ()
push (R l) = do
	emit [0x50 + index l]
push _ = raise "Can only push a register"

pop : Val -> X86 ()
pop (R l) = do
	emit [0x58 + index l]
pop _ = raise "Can only pop into a register"

call : Val -> X86 ()
call (A addr) = do
	emit [0x83]
	let src = memoff !('jit :- get) --'
	imm (prim__subB64 (prim__zextB32_B64 addr) (prim__addB64 src (the Bits64 5)))
call (R reg) = do
	emit [0xFF]
	emit [0xD0 + index reg]
call _ = do
	raise "Can only call addresses or registers"

mul : Val -> X86 ()
mul (R l) = do
	emit [0x48]
	emit [0xF7]
	emit [0xE0 `orBits8` index l]
mul _ = raise "Can only mul a register, perhaps you want imul?"

imul : Val -> Val -> X86 ()
imul (R l) (I r) = do
	emit [0x48]
	emit [0x69]
	emit [0xC0 `orBits8` index l]
	imm r
imul (R l) (R r) = do
	emit [0x48]
	emit [0x0F]
	emit [0xAF]
	emit [(0xC0 `orBits8` (shiftLeft' {n=1} (index r) 3)) `orBits8` (index l) ]
imul l r = raise {b=()} $ "Cannot imul " ++ show l ++ " by " ++ show r

mov : Val -> Val -> X86 ()
mov (R dst) (I src) = do
	emit [0x48]
	emit [0xC7]
	emit [0xC0 `orBits8` (index dst)]
	imm32 $ prim__truncB64_B32 src
mov (R dst) (A src) = do
	emit [0x48]
	emit [0xC7]
	emit [0xC7]
	imm $ prim__zextB32_B64 src
mov (R dst) (R src) = do
	emit [0x48]
	emit [0x89]
	emit [(0xC0 `orBits8` (shiftLeft' {n=1} (index src) 3)) `orBits8` (index dst) ]
mov (A dst) (I src) = do
	emit [0xC7]
	emit [0x04]
	emit [0x25]
	imm32 dst
	imm32 $ prim__truncB64_B32 src
mov l r = raise {b=()} $ "Cannot mov " ++ show r ++ " to " ++ show l

inc : Val -> X86()
inc (R l) = do
	emit [0x48]
	emit [0xFF]
	emit [0xC0 + index l]
inc _ = raise "Can only inc registers"

dec : Val -> X86()
dec (R l) = do
	emit [0x48]
	emit [0xFF]
	emit [0xc0 + (index l + 8)]
dec _ = raise "Can only inc registers"

jmp : Val -> X86 ()
jmp (A addr) = do
	emit [0xE9]
	let j = !('jit :- get) --'
	imm32 (prim__truncB64_B32 (prim__subB64 (memoff j) 
				((prim__addB64 (memptr j) (the Bits64 5)) )))
jmp _ = raise "Can only jump to an address"

cmp : Val -> Val -> X86 () 
cmp (R l) (I r) = do
	emit [0x48]
	emit [0x81]
	emit [0xF8 + index l]
	imm32 (prim__truncB64_B32 r)
cmp _ _ = raise "Unsupported cmp!"

jnz : Val -> X86 ()
jnz (A l) = do
	let pos_start = trunc' {m=64} {n=32} $ memoff !('jit :- get) --'
	let pos_end = the Bits32 l
	let pos_diff = pos_end - pos_start - (the Bits32 6)
	emit [0x0F]
	emit [0x85]
	imm32 pos_diff
jnz _ = raise "Can only jump to addresses"

jz : Val -> X86 ()
jz (A l) = do
	let pos_start = trunc' {m=64} {n=32} $ memoff !('jit :- get) --'
	let pos_end = the Bits32 l
	let pos_diff = pos_end - pos_start - (the Bits32 6)
	emit [0x0F]
	emit [0x85]
	imm32 pos_diff
jz _ = raise "Can only jump to addresses"

prologue : X86 ()
prologue = do
	push rbp
	mov rbp rsp

epilogue : X86 ()
epilogue = do
	mov rsp rbp
	pop rbp
	ret

label : X86 Val
label = let j = !('jit :- get) --'
	in pure (A (prim__truncB64_B32 (prim__subB64 (memoff j) (memptr j))))

jit : X86 ()
jit = do
	add (R RDX) (I 43)
	ret

runJit : X86 a -> Either String JITMem
runJit jitState = do
	let state = runInit ['jit := initialJIT 0, ()] (do --'
		jitState
		pure $ !('jit :- get)) --'
	case state of
		Left err => Left err
		Right jit => Right jit

