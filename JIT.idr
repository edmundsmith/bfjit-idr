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

record RunOptions where
	constructor RunOpts
	tapeSize : Int
	mach : List Bits8
	helpWanted : Bool
	inputFileName : Maybe String
	outputFileName : Maybe String
	shouldRun : Bool
	shouldCompile : Bool
	optLevel : Int
	showLLIR : Bool
	showMIR : Bool

parseRunOptsOver : List String -> RunOptions -> RunOptions
parseRunOptsOver options = 
	case options of
		("-O0"::xs) => (parseRunOptsOver xs) . record { optLevel = 0 }
		("-O1"::xs) => (parseRunOptsOver xs) . record { optLevel = 1 }
		("-O2"::xs) => (parseRunOptsOver xs) . record { optLevel = 2 }
		("-O3"::xs) => (parseRunOptsOver xs) . record { optLevel = 3 }
		("-O"::x::xs) => (parseRunOptsOver xs) . record { optLevel = the Int $ cast x }
		("-t"::x::xs) => (parseRunOptsOver xs) . record { tapeSize = the Int $ cast x }
		("-h"::xs) => (parseRunOptsOver xs) . record { helpWanted = True }
		("--help"::xs) => (parseRunOptsOver xs) . record { helpWanted = True }
		("-o"::x::xs) => (parseRunOptsOver xs) . record { outputFileName = Just x }
		("-c"::xs) => (parseRunOptsOver xs) . record { shouldCompile = True, shouldRun = False }
		("--dry-run"::xs) => (parseRunOptsOver xs) . record { shouldRun = False }
		("--show-llir"::xs) => (parseRunOptsOver xs) . record { showLLIR = True }
		("--show-mir"::xs) => (parseRunOptsOver xs) . record { showMIR = True }
		(x::xs) => (parseRunOptsOver xs) . record { inputFileName = Just x }
		_ => id

defaultRunOpts : RunOptions
defaultRunOpts = RunOpts 30000 [] False Nothing Nothing True False 0 False False

Show RunOptions where 
	show (RunOpts tapeSize mach helpWanted inputFileName outputFileName shouldRun shouldCompile optLevel showLLIR showMIR) = 
		"RunOptions {" ++ 
			" tapeSize = " ++ show tapeSize ++
			", mach = " ++ show mach ++
			", helpWanted = " ++ show helpWanted ++
			", inputFileName = " ++ show inputFileName ++
			", outputFileName = " ++ show outputFileName ++
			", shouldRun = " ++ show shouldRun ++
			", shouldCompile = " ++ show shouldCompile ++
			", optLevel = " ++ show optLevel ++
			", showLLIR = " ++ show showLLIR ++
			", showMIR = " ++ show showMIR ++ " }"


makeElfFromJit : RunOptions -> List Bits8 -> List Bits8
makeElfFromJit options mach = with Prelude.List do
	
	let mach = drop 10 mach --Skip the initial hardcoded 'mov rax, lit64' prologue
	--case isLTE 1 (length mach1) of
		--Yes prf => do
	let mach = take (case (length mach) of (S n) => n; Z => Z) mach --Drop final ret epilogue

	let prologue = the (List Bits8) [ --Establish buffer addr on rax
			0x48,0x31,0xFF, --xor rdi, rdi //rdi=0
			0xBE
		] ++ (reverse $ b32ToBytes $ prim__zextInt_B32 $ tapeSize options) ++ --mov rsi, (tapeSize options)
			[0xBA,0x03,0x00,0x00,0x00, --mov rdx, 3 (R|W)
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
			0x78, 0x00, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, -- 8 byte offset for program start
			--0x20:
			0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, --program header table offset
			-- (immediately follows elf table)
			0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, -- 8 byte offset for section header table start
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
	
	
	elfHeader ++ progHeader ++ prologue ++ mach ++ epilogue

compileBF : RunOptions -> String -> Effects.SimpleEff.Eff (List MIR) [STDIO]
compileBF runOpts fileContents = do
	let llir = parseLLIR fileContents

	if showLLIR runOpts
		then putStrLn (show llir)
		else pure ()
	
	let mir = elevateLLIR llir
	let mir = (mkOpt (optLevel runOpts) mir)

	if showMIR runOpts
		then putStrLn (show mir)
		else pure ()

	pure mir

runJit : RunOptions -> String -> Effects.SimpleEff.Eff () [STDIO, MMAP, MALLOC (), IOEFF ()]
runJit runOpts fileContents = do

	tapePtr <- calloc (tapeSize runOpts)
						
	let tapeLoc = bytesToB64 $ reverse $ b64ToBytes (unsafePerformIO $ (foreign FFI_C "labs" (Ptr -> IO Bits64) tapePtr))

	mir <- compileBF runOpts fileContents

	let readyJit = emitterMIR tapeLoc mir
	let jitLen = toIntNat $ length readyJit
	
	jitBuf <- mmap_exe (ARRAY jitLen I8)

	--putStrLn "Writing bytes"
	efor_ {b=()} (zip (the (List Int) [0..jitLen]) readyJit) $ \(off, byte) => 
		lift $ performIO $ poke I8 (CPt jitBuf off) byte

	
	--efor_ {b=()} (makeElfFromJit (MakeElfCommand 0 readyJit) readyJit) $ \byte =>
	--	lift $ performIO $ do foreign FFI_C "printf" (String -> Bits8 -> IO Int) "%c" byte; pure ()
	
	lift $ performIO $ do run_int_int_ptr jitBuf 0; pure ()

	_ <- munmap jitBuf (prim__zextInt_B64 jitLen)
	free tapePtr

	pure ()

writeToFile : String -> Ptr -> Bits64 -> Effects.SimpleEff.Eff () [IOEFF (), MALLOC Ptr]
writeToFile fname buf len = performIO $ do
	Right (FHandle handle) <- fopen fname "wb" | Left err => pure ()
	(foreign FFI_C "fwrite" (Ptr -> Bits64 -> Bits64 -> Ptr -> IO ()) 
		buf 1 len handle)
	closeFile (FHandle handle)

maybeWriteToFile : Maybe String -> Ptr -> Bits64 -> Effects.SimpleEff.Eff () [IOEFF (), MALLOC Ptr]
maybeWriteToFile (Just str) buf len = writeToFile str buf len
maybeWriteToFile Nothing _ _  = pure ()

runCompile : RunOptions -> String -> Effects.SimpleEff.Eff () [STDIO, FILE (), IOEFF (), MALLOC ()]
runCompile runOpts fileContents = do
	
	mir <- compileBF runOpts fileContents
	
	let readyBin = emitterMIR 0 mir
	let elfBin = makeElfFromJit defaultRunOpts readyBin
	lift $ with Prelude.Strings do
		putStrLn $ "Compiling " ++ show (map {f=List} (prim__intToChar . prim__zextB8_Int) elfBin)
		putStrLn $ " to " ++ (pack (map (prim__intToChar . prim__zextB8_Int) elfBin))
		

	let elfL = map (prim__intToChar . prim__zextB8_Int) elfBin
	let elfLength = toIntNat $ Prelude.List.length elfL
	--Strings are null-unfriendly in Idris, so use a buffer instead
	elfBuf <- calloc elfLength

	--write to file
	{-lift $ case outputFileName runOpts of
		Just filename => putStrLn ""
			case (lift $ performIO $ the (IO $ Either String ()) $ do
				Right (FHandle handle) <- fopen fileName "wb" | Left err => Left err
				(foreign FFI_C "fwrite" (Ptr -> Bits64 -> Bits64 -> Ptr -> IO ()) 
					elfBuf 1 elfLength handle)
				closeFile (FHandle handle)) of
				Left err => putStrLn err
				Right () => pure ()
		Nothing => putStrLn "Need an output file name"
	-}
	{-case outputFileName runOpts of
		Just fname => lift $ writeToFile fname elfBuf elfLength
		Nothing => lift $ the (Eff () [IOEFF (), MALLOC Ptr]) (pure ())-}
	efor_ {b=()} (zip (the (List Int) [0..elfLength]) elfBin) $ \(off, byte) => 
		lift $ performIO $ poke I8 (CPt elfBuf off) byte
	lift $ maybeWriteToFile (outputFileName runOpts) elfBuf (prim__zextInt_B64 elfLength)

	free elfBuf
	pure ()

printHelpMessage : List String -> Eff () [STDIO]
printHelpMessage opts = if elem "help" opts then putStrLn helpMessage else pure ()

emain : Effects.SimpleEff.Eff () [SYSTEM, STDIO, FILE (), MMAP, MALLOC (), IOEFF ()]
emain = with Effect.File do
	case !getArgs of
		[] => putStrLn "Impossible: empty arg list"
		(prog::args) => do
			let runOpts = parseRunOptsOver args defaultRunOpts
			
			lift $ putStrLn $ show runOpts

			if helpWanted runOpts
				then putStrLn helpMessage
				else pure ()

			case inputFileName runOpts of
				Nothing => putStrLn "Need an input file name"
				Just file => do
					case !(readFile file) of 
						Result fileContents => do
							if shouldRun runOpts
								then runJit runOpts fileContents
								else pure ()
							if shouldCompile runOpts
								then runCompile runOpts fileContents
								else pure ()
							pure ()

						err => putStrLn ("Unexpected error with: " ++ file)

io_emain : IO ()
io_emain = run emain
