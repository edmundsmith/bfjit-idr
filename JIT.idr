module JIT

import Effects
import Effect.State
import Effect.File
import Effect.StdIO
import Effect.System
import Effect.Exception
--import Effect.Memory
import Data.Bits

import Assembler
import CFFI
import BF
import MMap
import Malloc

import Debug.Trace


%include C "stdlib.h"
%include C "stdio.h"

%access public export


data IOEff : Type -> Effect where
	PerformIO : IO a -> NoResourceEffect.sig (IOEff a) ()

Handler (IOEff a) IO where
	handle ctx (PerformIO io) k = do x <- io; k () ()

IOEFF : Type -> EFFECT
IOEFF a = MkEff () (IOEff a)

performIO : IO a -> Effects.SimpleEff.Eff () [IOEFF a]
performIO io = call $ PerformIO io



{-run_fptr : %static {fptr:Type} -> CPtr -> fptr
run_fptr {fptr} ptr = case fptr of 
	(b -> c) => the (b->c) $ \x:b => foreign FFI_C "%dynamic" (Ptr -> b -> c) ptr x
	(a -> b -> c) => \x => run_fptr {fptr=b->c} ptr -}
run_int_int_ptr : CPtr -> Int -> IO Int
run_int_int_ptr ptr = foreign FFI_C "%dynamic" (Ptr -> Int -> IO Int) ptr

setAndExecuteBits : List Bits8 -> Composite -> CPtr -> IO ()
setAndExecuteBits bits arr ptr = do
		putStrLn "Setting bytes"
		loopFrom' 0 bits ptr
		putStrLn "\nWow!"
		putStrLn $ show !(run_int_int_ptr ptr 0)
		pure ()

	where
	loopFrom' : Int -> List Bits8 -> CPtr -> IO ()
	loopFrom' n (h::t) (CPt p o) = do
		poke I8 (CPt p (o + (sizeOf (fieldType arr Z) * n))) h
		loopFrom' (n+1) t (CPt p o)
	loopFrom' n [] ptr = pure ()

executeJit : List Bits8 -> Eff () [MMAP, IOEFF ()]
executeJit bits = do
	let lbits = toIntNat $ S $ length bits
	let arrTy = the Composite (ARRAY lbits (T I8))
	let ptrLen = prim__zextInt_B64 $ sizeOf arrTy
	--withMMap arrTy (setAndExecuteBits bits arrTy)
	let ptr = !(mmap_exe arrTy)
	let res = !(lift $ performIO $ setAndExecuteBits bits arrTy ptr)
	let ig = !(munmap ptr ptrLen)
	pure ()

factorial : Bits64 -> X86 ()
factorial n = do
	mov rcx (I n)
	mov rax (I 1)
	loop <- label
	mul rcx
	dec rcx
	cmp rcx (I 0)
	jnz loop
	ret

efor_ : List a -> (a -> Eff b effList) -> Eff () effList
efor_ (h::t) f = (f h) >>= \_ => (efor_ t f)
efor_ [] _ = pure ()

parseOpts : List String -> (List String, List String)
parseOpts l = parseOpts' (map unpack l) ([],[]) where
	parseOpts' : List (List Char) -> (List String, List String) -> (List String, List String)
	parseOpts' (with List ('-'::'-'::h)::t) (l,r) = parseOpts' t ((pack h)::l,r)
	parseOpts' (h::t) (l,r) = parseOpts' t (l, (pack h)::r)
	parseOpts' [] res = res

helpMessage : String
helpMessage = "BFJIT - Interpret a BF program\nFormat:\n\n" ++
	"    bjfit [--o=n] filename*\n" ++
	"    --o=   JIT Optimisation level\n" ++
	"           Supported optimisation levels: [0, 1, 2]"

record MakeElf where
	constructor MakeElfCommand
	tapeSize : Int
	mach : List Bits8


makeElfFromJit : MakeElf -> List Bits8 -> List Bits8
makeElfFromJit options mach = with Prelude.List do
	
	let mach = drop 10 mach --Skip the initial hardcoded 'mov rax, lit64' prologue
	--case isLTE 1 (length mach1) of
		--Yes prf => do
	let amount = case (length mach) of (S n) => n; Z => Z
	let mach = take amount mach --Drop final ret epilogue

	let prologue = the (List Bits8) [ --Establish buffer addr on rax
			0x48,0x31,0xFF, --xor rdi, rdi //rdi=0
			0xBE,0x30,0x75,0x00,0x00, --mov rsi, 30000
			0xBA,0x03,0x00,0x00,0x00, --mov rdx, 3 (R|W)
			0x41,0xBA,0x22,0x00,0x00,0x00, --mov r10, 0x22 (ANONYMOUS|PRIVATE)
			0x49,0xC7,0xC0,0xFF,0xFF,0xFF,0xFF, --mov r8, (-1) //fd
			0x41,0xB9,0x00,0x00,0x00,0x00, --mov r9, 0 //offset
			0xB8,0x09,0x00,0x00,0x00, --mov rax, 9 //sys_mmap
			0x0F,0x05, --syscall (mmap)
			0x48,0x89,0xC3 --mov rbx, rax //save mmap ptr for later (rax is mut'd)
		]
	let epilogue = the (List Bits8) [
			0x48,0x89,0xDF, --mov rdi, rbx
			0xBE,0x30,0x75,0x00,0x00, --mov rsi, 30000
			0xB8,0x0B,0x00,0x00,0x00, --mov rax, 11 (sys_munmap)
			0x0F,0x05, --syscall (munmap)
			0xB8,0x3C,0x00,0x00,0x00, --mov rax, 60 (sys_exit)
			0x48,0x31,0xFF, --xor rdi, rdi //rdi=0
			0x0F,0x05 --syscall (exit)
		]

	let elfHeader = the (List Bits8) [
			--0x00:
			0x7F, 0x45, 0x4C, 0x46, --Elf magic number
			0x02, --64 bits
			0x01, --Little endian
			0x01, --Elf version
			0x00, --Targetting generic platform
			0x00, --ABI version (ignored on linux)
			0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, --Padding, unused
			--0x10:
			0x02, 0x00, --e_type is executable, little endian
			0x3E, 0x00, --e_machine - ISA is x64
			0x01, 0x00, 0x00, 0x00, --Version, again is 1
			            --v Post-virtual-setup pointer, not raw file offset
			0xB8, 0x00, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, -- 8 byte offset for program start
			--0x20:
			0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, --program header table offset
			-- (immediately follows elf table)
			0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, -- 8 byte offset for section header table start
			--0x30:
			0x00, 0x00, 0x00, 0x00, -- Flags (not defined for linux)
			0x40, 0x00, --Total size of this header (64 bytes on 64 bit, 52 on 32 bit)
			0x38, 0x00, --2 byte size of program header table entry
			0x01, 0x00, --2 byte number of program header table entries
			0x40, 0x00, --2 byte size of section header table entry
			0x00, 0x00, --2 byte number of section header table entries
			0x00, 0x00 --2 byte index of section header table entry with section names
			--0x40:
		]

	let progHeader = the (List Bits8) [
			--0x00:
			0x01,0,0,0, --p_type is PT_LOAD
			0x05,0,0,0, --p_flags is R|X
			0,0,0,0,0,0,0,0, --8 bytes offset where the program is to be found
			--0x10:
			0,0,0x20,0,0,0,0,0,
			--VADDR, --8 bytes virtual address of the segment
			0,0,0x20,0,0,0,0,0] ++ --8 bytes Physical addr (irrelevant?)
			--0x20:
			reverse (b64ToBytes 
				(prim__zextInt_B64 $ toIntNat $ (length mach + length prologue + length epilogue) + {-sizeof elfHeader + progHeader-} 184)) ++
			--FILESIZE, --8 byte file size
			reverse (b64ToBytes 
				(prim__zextInt_B64 $ toIntNat $ (length mach + length prologue + length epilogue) + {-sizeof elfHeader + progHeader-} 184)) ++
			--MEMSIZE, --8 byte memory space taken up
			--0x30:
			[0,0,0x20,0,0,0,0,0] --byte alignment
	{-let shstrtabSectHeader = the (List bits8) [
		--0x00:
		0x00,0x00,0x00,0x00, --Name index in shstrtab
		0x03,0x00,0x00,0x00, --Type is SHT_STRTAB

	]-}
	let sectionHeader = the (List Bits8) [
			--0x00:
			0,0,0,0, -- Section name index in shstrtab
			0,0,0,0, -- Null header
			0,0,0,0,0,0,0,0, -- Section header flags
			--0x10:
			0,0,0,0,0,0,0,0, -- Virtual address of section if loaded
			0x78,0,0,0,0,0,0,0, -- Offset of section in image
			--0x20:
			0,0,0,0,0,0,0,0, -- Size of the section
			0,0,0,0, -- sh-Link
			0,0,0,0, -- sh_info
			--0x30:
			0x8,0,0,0,0,0,0,0, -- Alignment of the section
			0,0,0,0,0,0,0,0 -- sh_entsize
			--0x40:
			]

	
	elfHeader ++ progHeader ++ sectionHeader ++ prologue ++ mach ++ epilogue


	

printHelpMessage : List String -> Eff () [STDIO]
printHelpMessage opts = if elem "help" opts then putStrLn helpMessage else pure ()

emain : Effects.SimpleEff.Eff () [SYSTEM, STDIO, FILE (), MMAP, MALLOC (), IOEFF ()]
emain = 
	case !getArgs of
		[] => putStrLn "Impossible: empty arg list"
		(prog::args) => do
			let (opts, files) = parseOpts args
			printHelpMessage opts
			let irOpt = optPassMIRFor opts
			--putStrLn $ "Opts: " ++ show opts
			efor_ {b=()} files $ \file => with Effect.StdIO with Effect.File do --'
				--putStrLn $ "Running " ++ file
				case !(readFile file) of 
					Result fileContents => do
						--putStrLn "Read:"
						--putStrLn fileContents

						tapePtr <- calloc 4000
						
						let tapeLoc = bytesToB64 $ reverse $ b64ToBytes (unsafePerformIO $ (foreign FFI_C "labs" (Ptr -> IO Bits64) tapePtr))

						let llir = parseLLIR fileContents

						let mir = elevateLLIR llir

						{-let mir = optIR @{fixLoops} $ optIR @{mergeImm} mir
						let mir = optIR @{reorderFixedLoops} mir
						let mir = optIR @{removeNops} $ optIR @{mergeImm} $ optIR @{maddifyLoops} $ mir
						-}

						let mir = (optPassMIRFor opts mir)
						--putStrLn $ show mir
						let readyJit = emitterMIR tapeLoc mir
						let jitLen = toIntNat $ length readyJit
						
						jitBuf <- mmap_exe (ARRAY jitLen I8)

						--putStrLn "Writing bytes"
						efor_ {b=()} (zip (the (List Int) [0..jitLen]) readyJit) $ \(off, byte) => 
							lift $ performIO $ poke I8 (CPt jitBuf off) byte

						--putStrLn "Begin elf:"

						efor_ {b=()} (makeElfFromJit (MakeElfCommand 0 readyJit) readyJit) $ \byte =>
							lift $ performIO $ do foreign FFI_C "printf" (String -> Bits8 -> IO Int) "%c" byte; pure ()
						--lift $ performIO $ do _ <- foreign FFI_C "printf" (String -> Ptr -> IO Int) "%s\n" jitBuf; pure ()

						--putStrLn $ show mir
						--putStrLn "---------"
										
						--putStrLn "\nMIR:"
						--for_ readyMIRJit (Prelude.Interactive.putStr . show)
						--putStrLn "Jit prepared!"
						--performIO $ do _ <- run_int_int_ptr jitBuf 0; pure ()

						_ <- munmap jitBuf (prim__zextInt_B64 jitLen)
						free tapePtr

					err => putStrLn ("Unexpected error with: " ++ file)

io_emain : IO ()
io_emain = run emain
