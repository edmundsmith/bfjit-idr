module BF

--import Util
--import Unlifter
import Assembler
import Effects
import Effect.State
import Effect.File
import Effect.StdIO
import Effect.Exception

%access public export

infixl 9 |>
infixr 0 <|


||| Pipeline style function application, useful for chaining
||| functions into a series of transformations, reading top
||| to bottom.
|||
||| ```idris example
||| [[1], [2], [3]] |> join |> map (* 2)
||| ```
(|>) : a -> (a -> b) -> b
a |> f = f a


||| Backwards pipeline style function application, similar to $.
|||
||| ```idris example
||| unpack <| "hello" ++ "world"
||| ```
(<|) : (a -> b) -> a -> b
f <| a = f a

data LLIR = LL_Left
	| LL_Right
	| LL_Inc
	| LL_Dec
	| LL_OpenLoop
	| LL_CloseLoop
	| LL_Input
	| LL_Output

Eq LLIR where
	(==) LL_Left LL_Left = True
	(==) LL_Right LL_Right = True
	(==) LL_Inc LL_Inc = True
	(==) LL_Dec LL_Dec = True
	(==) LL_OpenLoop LL_OpenLoop = True
	(==) LL_CloseLoop LL_CloseLoop = True
	(==) LL_Input LL_Input = True
	(==) LL_Output LL_Output = True
	(==) _ _ = False

record LLTape where
	constructor MkLLTape
	llTape : List Bits8

record LLProg where
	constructor MkLLProg
	llProg : List LLIR

record LLInterpreter where
	constructor MkInterpreter

total
isCharBF : 
Char -> Bool
isCharBF c = elem c (unpack "<>,.[]+-")

--total
--proveIsCharBF : (c:Char) -> (c ** (isCharBF c) = True)
--proveIsCharBF c = (c ** isCharBF c)

total
charToLLIR : (c:Char) -> {auto prf : isCharBF c = True} -> LLIR
charToLLIR '<' = LL_Left
charToLLIR '>' = LL_Right
charToLLIR '+' = LL_Inc
charToLLIR '-' = LL_Dec
charToLLIR '[' = LL_OpenLoop
charToLLIR ']' = LL_CloseLoop
charToLLIR ',' = LL_Input
charToLLIR '.' = LL_Output
charToLLIR _ {prf=prf} = LL_Output

total
parseLLIR : String -> List LLIR
parseLLIR str = reverse $ foldl combine [] (unpack str) where
	combine : List LLIR -> Char -> List LLIR
	combine list c = case decEq (isCharBF c) True of
		Yes prf => charToLLIR c :: list
		No contra => list

{-
	rax : cell*
	
-}
 
emitterLLIR : Bits64 -> List LLIR -> List Bits8
emitterLLIR memAddr list = 
		case runJit (emitter list) of
			Left err => []
			Right jit => mach $ record { 
				mach = (([0x48,0xB8] ++ (b64ToBytes memAddr)) ++ (mach jit)),
				memoff $= (+10)
			} jit
	where
	emitter : List LLIR -> X86 ()
	emitter (LL_Left::t) = do
		sub rax (I 1)
		emitter t
	emitter (LL_Right::t) = do
		add rax (I 1)
		emitter t
	emitter (LL_Inc::t) = do
		emit [0x80,0x00,0x01]	--add byte [rax], 1
		emitter t
	emitter (LL_Dec::t) = do
		emit [0x80,0x28,0x01]	--sub byte [rax], 1
		emitter t 
	emitter (LL_Output::t) = do
		push rax
		mov rdi (I 1)
		mov rsi rax
		mov rdx (I 1)
		mov rax (I 1)
		syscall
		pop rax
		emitter t
	emitter (LL_Input::t) = do
		push rax
		mov rdi (I 0)
		mov rsi rax
		mov rdx (I 1)
		mov rax (I 0)
		syscall
		pop rax
		emitter t
	emitter (LL_OpenLoop::t) = do
		let inner = runJit $ emitter t
		case inner of
			Left err => raise err
			Right ijit => do
				emit [0x80,0x38,0x00] -- cmp byte [rax], 0x0
				emit [0x0F]
				emit [0x84]
				imm32 $ (prim__zextInt_B32 $ toIntNat $ length $ mach ijit)
				emit $ mach ijit
				case tail' (dropWhile (/= LL_CloseLoop) t) of
					Just tail => emitter tail
					Nothing => pure ()
	emitter (LL_CloseLoop::t) = do
		emit [0x80,0x38,0x00] -- cmp byte [rax], 0x0
		-- (-3) is the offset to make up for the 9 unincluded openloop prolog bytes
		-- jnz
		emit [0x0F]
		emit [0x85]
		imm32 $ prim__subB32 (the Bits32 (-4)) $ prim__zextInt_B32 $ toIntNat $ length $ mach !('jit :- get) --'
		--jnz $ A $ ((the Bits32 (-3)) +) $ prim__zextInt_B32 $ negate $ toIntNat $ length $ mach !('jit :- get) --'
	emitter [] = ret

{-record LLIR_Interpreter (m:Type -> Type) : Type* where
	constructor MkLLInterpreter
	tapeLength : Nat
	steps : Nat
	gas : Nat
	tape : InfTape Bits8
	tapeHeadPos : Integer
	tapeHeadPosMax, tapeHeadPosMin : Integer
	backtrackCount : Nat
	programTape : FinTape Z (pred tapeLength) LLIR
	ioInput : m Char
	ioOutput : List Char

jLoopClose : LLIR_Interpreter -> LLIR_Interpreter
jLoopClose interpreter = jLoopClose' interpreter (backtrackCount interpreter) where
	jLoopClose' : LLIR_Interpreter -> Nat -> LLIR_Interpreter
	jLoopClose' interpreter initialScope = case cursor (programTape interpreter) of
		LL_CloseLoop => case backtrackCount interpreter of
			initialScope => record { programTape $= tapeRight } interpreter
			_ => jLoopClose' (record { backtrackCount $= pred, programTape $= tapeRight } interpreter) initialScope
		LL_OpenLoop => jLoopClose' (record { backtrackCount $= S, programTape $= tapeRight } interpreter) initialScope
		_ => jLoopClose' (record { programTape $= tapeRight } interpreter) initialScope

Interpreter (List LLIR) (LLIR_Interpreter IO) (IO ()) where
	initial instrs = MkLLInterpreter (length instrs) Z 100000000 [] Z
		(FinTape [] (head instrs) (fromList $ reverse $ tail instrs)) (pure ()) []
	step interpreter = ?hmm --do
		let tapeOffset = the (Integer, InfTape Bits8 -> InfTape Bits8) $ 
			case cursor (programTape interpreter) of
				LL_Left => (-1, infTapeLeft)
				LL_Right => (1, infTapeRight)
				_ => (0, id)
		let pos' = tapeHeadPos interpreter + (first tapeOffset)
		let dBacktrack = case cursor (programTape interpreter) of
			LL_OpenLoop => -1
			LL_CloseLoop => 1
			_ => 0


		record {
			steps $= S
			gas $= pred
			tape $= second tapeOffset
			tapeHeadPos $= \tapeHeadPos 
			tapeHeadPosMin $= min pos'
			tapeHeadPosMax $= max pos'
			backtrackCount $= dBacktrack
		} interpreter

		interpreter
		|> record { steps $= S, gas $= pred }
		|> case cursor (programTape interpreter) of
			LL_Left =>  record { tapeHeadPos $= (- 1) }
					|>	\i => record { tapeHeadPosMin $= min (tapeHeadPos i) } i
					|>	record {	tape $= infTapeLeft,
									programTape $= tapeRight }
			LL_Right => record { tapeHeadPos $= (+ 1) }
					|>	\i => record { tapeHeadPosMax $= max (tapeHeadPos i) } i
					|>	record {	tape $= infTapeRight,
									programTape $= tapeRight }
			LL_Inc =>	record { 	tape $= updateCursor (prim__addB8 1) }
			LL_Dec => 	record { 	tape $= updateCursor (prim__subB8 1) }
			LL_OpenLoop => record {}
			LL_Input => record {	tape $= updateCursor ()}

	-}
