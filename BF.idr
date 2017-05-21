module BF

--import Util
--import Unlifter
import Assembler
import Effects
import Effect.State
import Effect.File
import Effect.StdIO
import Effect.Exception

import Debug.Trace

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

Show LLIR where
	show LL_Left = "LL_Left"
	show LL_Right = "LL_Right"
	show LL_Inc = "LL_Inc"
	show LL_Dec = "LL_Dec"
	show LL_OpenLoop = "LL_OpenLoop"
	show LL_CloseLoop = "LL_CloseLoop"
	show LL_Input = "LL_Input"
	show LL_Output = "LL_Output"

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

data MIR : Type where
	M_Move : Int -> MIR
	M_Add : Bits8 -> MIR
	M_Input : MIR
	M_Output: MIR
	M_Loop : List MIR -> MIR
	M_FixedLoop : List MIR -> MIR
	M_Set : Bits8 -> MIR
	M_MulAddOff : Bits8 -> Int -> MIR

Eq MIR where
	(==) (M_Move m) (M_Move n) = m == n
	(==) (M_Add m) (M_Add n) = m == n
	(==) (M_Input) (M_Input) = True
	(==) (M_Output) (M_Output) = True
	(==) (M_Loop l1) (M_Loop l2) = assert_total $ l1 == l2
	(==) (M_FixedLoop l1) (M_FixedLoop l2) = assert_total $ l1 == l2
	(==) (M_Set m) (M_Set n) = m == n
	(==) (M_MulAddOff mul1 off1) (M_MulAddOff mul2 off2) = mul1 == mul2 && off1 == off2
	(==) _ _ = False

Show MIR where
	show (M_Move m) = "M_Move " ++ show m
	show (M_Add m) = "M_Add " ++ show m
	show (M_Input) = "M_Input"
	show (M_Output) = "M_Output"
	show (M_Loop l1) = "M_Loop " ++ show l1
	show (M_FixedLoop l1) = "M_FixedLoop " ++ show l1
	show (M_Set m) = "M_Set " ++ show m
	show (M_MulAddOff mul1 off1) = "M_MulAddOff " ++ show mul1 ++ " " ++ show off1

total
tapeOff : MIR -> Maybe Int
tapeOff (M_Add _) = Just 0
tapeOff (M_Input) = Just 0
tapeOff (M_Output) = Just 0
tapeOff (M_FixedLoop _) = Just 0
tapeOff (M_Set _) = Just 0
tapeOff (M_MulAddOff _ _) = Just 0
tapeOff (M_Move m) = Just m
tapeOff (M_Loop l) = assert_total $ case foldl (liftA2 (+)) (Just 0) (map tapeOff l) of
	Just 0 => Just 0
	_ => Nothing

total
isIO : MIR -> Bool
isIO M_Input = True
isIO M_Output = True
isIO _ = False

total
isTransitiveIO : MIR -> Bool
isTransitiveIO (M_Loop l) = assert_total $ any isTransitiveIO l
isTransitiveIO (M_FixedLoop l) = assert_total $ any isTransitiveIO l
isTransitiveIO M_Input = True
isTransitiveIO M_Output = True
isTransitiveIO _ = False

total
isOrderBarrier : MIR -> Bool
isOrderBarrier (M_Loop _) = True
isOrderBarrier _ = False

total
takeBalanced : List LLIR -> List LLIR
takeBalanced [] = []
takeBalanced (LL_CloseLoop::t) = t
takeBalanced (LL_OpenLoop::t) = assert_total $ takeBalanced $ takeBalanced t
takeBalanced (h::t) = takeBalanced t

total
parseLLIR : String -> List LLIR
parseLLIR str = reverse $ foldl combine [] (unpack str) where
	combine : List LLIR -> Char -> List LLIR
	combine list c = case decEq (isCharBF c) True of
		Yes prf => charToLLIR c :: list
		No contra => list

total
elevateLLIR : List LLIR -> List MIR
elevateLLIR [] = []
elevateLLIR (LL_Left::tail) = (M_Move (-1)) :: (elevateLLIR tail)
elevateLLIR (LL_Right::tail) = (M_Move 1) :: (elevateLLIR tail)
elevateLLIR (LL_Inc::tail) = (M_Add 1) :: (elevateLLIR tail)
elevateLLIR (LL_Dec::tail) = (M_Add (0xff)) :: (elevateLLIR tail)
elevateLLIR (LL_OpenLoop::tail) = assert_total $ (M_Loop (elevateLLIR tail)) :: (elevateLLIR $ takeBalanced tail)
elevateLLIR (LL_CloseLoop::tail) = []
elevateLLIR (LL_Input::tail) = (M_Input) :: (elevateLLIR tail)
elevateLLIR (LL_Output::tail) = (M_Output) :: (elevateLLIR tail)

{-
	rax : cell*
	
-}
 
emitterLLIR : Bits64 -> List LLIR -> List Bits8
emitterLLIR memAddr list = 
		case runJit (emitter list) of
			Left err => []
			Right jit => trace (show $ length $ mach jit) mach $ record { 
				mach = (([0x48,0xB8] ++ (b64ToBytes memAddr)) ++ (mach jit)),
				memoff $= (+10)
			} jit
	where
	
	--TODO: Thread explicit not-consumed LLIR list through
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
				let balanced = takeBalanced t
				case balanced of
					[] => ret
					tail => emitter tail
	emitter (LL_CloseLoop::t) = do
		emit [0x80,0x38,0x00] -- cmp byte [rax], 0x0
		-- (-3) is the offset to make up for the 9 unincluded openloop prolog bytes
		-- jnz
		emit [0x0F]
		emit [0x85]
		imm32 $ prim__subB32 (the Bits32 (-4)) $ prim__zextInt_B32 $ toIntNat $ length $ mach !('jit :- get) --'
		--jnz $ A $ ((the Bits32 (-3)) +) $ prim__zextInt_B32 $ negate $ toIntNat $ length $ mach !('jit :- get) --'
	emitter [] = ret

record LLTape where
	constructor MkLLTape
	llTape : List Bits8

record LLProg where
	constructor MkLLProg
	llProg : List LLIR

record LLInterpreter where
	constructor MkInterpreter

interface Opt (f:Type -> Type) irLevel (aggressiveness : Nat) where
	optIR : f irLevel -> f irLevel

[mergeImm] Opt List MIR 1 where
	optIR list = performOpt list where
		performOpt : List MIR -> List MIR
		performOpt ((M_Add a)::(M_Add b)::t) = performOpt $ (M_Add (a+b))::t
		performOpt ((M_Move a)::(M_Move b)::t) = performOpt $ (M_Move (a+b))::t
		performOpt ((M_Loop l)::(M_Loop _)::t) = performOpt $ (M_Loop l)::t
		performOpt ((M_FixedLoop l)::(M_Loop _)::t) = performOpt $ (M_FixedLoop l)::t
		performOpt ((M_Loop l)::(M_FixedLoop _)::t) = performOpt $ (M_Loop l)::t
		performOpt ((M_FixedLoop l)::(M_FixedLoop _)::t) = performOpt $ (M_FixedLoop l)::t
		performOpt ((M_Loop [(M_Add 0xff)])::t) = performOpt $ (M_Set 0) :: t
		performOpt ((M_FixedLoop [(M_Add 0xff)])::t) = performOpt $ (M_Set 0) :: t
		performOpt ((M_Set _)::(M_Set v)::t) = performOpt $ (M_Set v)::t
		performOpt ((M_Loop l)::t) = (M_Loop (performOpt l)) :: (performOpt t)
		performOpt ((M_FixedLoop l)::t) = (M_FixedLoop (performOpt l)) :: (performOpt t)
		performOpt (h::t) = h :: performOpt t
		performOpt [] = []

[fixLoops] Opt List MIR 1 where
	optIR list = performOpt list where
		performOpt : List MIR -> List MIR
		performOpt ((M_Loop l)::t) = case tapeOff (M_Loop l) of
			Just 0 => (M_FixedLoop (performOpt l)) :: (performOpt t)
			Just n => (M_FixedLoop ((performOpt l) ++ [M_Move (-n)])) :: (performOpt t)
			Nothing => (M_Loop (performOpt l)) :: (performOpt t)
		performOpt (h::t) = h :: (performOpt t)
		performOpt [] = []

[reorderFixedLoops] Opt List MIR 2 where
	optIR list = (if not (elemBy (\_,x => case x of 
			M_Loop _ => True
			M_MulAddOff _ _ => True
			_ => False) (M_Set 0) list) then performOpt else id) (map innerOpt list)
	where
		{-buildList : Int -> List MIR -> (List (List MIR), List (List MIR)) -> List (List MIR)
		buildList 0 [] (l, r) = [[M_Move (-1 - (toIntNat $ length l))]] ++ reverse l ++ r ++ [[M_Move (-1)]]
		buildList n [] (l, r) = reverse ([M_Move (-1-n)] :: ((map reverse r)) ++ (reverse (map reverse l)))
		buildList n ((M_FixedLoop loop)::t) (l, r) = with List
			buildList n t (l, (M_FixedLoop (performOpt loop)::(the (List MIR) $ fromMaybe [] (head' r)))::fromMaybe [] (tail' r))
		buildList n ((M_Move 0)::t) (l, r) = buildList n t (l, r)
		buildList n ((M_Move m)::t) (l, r) = if m > 0
			then buildList (n+1) ((M_Move (m-1))::t) ((fromMaybe [] (head' r))::l, fromMaybe [] (tail' r))
			else buildList (n-1) ((M_Move (m+1))::t) (fromMaybe [] (tail' l), (fromMaybe [] (head' l))::r)
		buildList n (h::t) (l, r) = buildList n t (l, (h::(fromMaybe [] (head' r)))::(fromMaybe [] (tail' r)))
		-}
		tagList' : List MIR -> Eff (List (Int, MIR), (Int, MIR), List MIR) [STATE Int]
		tagList' [] = pure ([], (0, M_Move 0), [])
		tagList' ((M_Move n)::t) = do
			update (+n)
			tagList' t
		tagList' ((M_Loop l)::t) = do 	--Loops are rewrite barriers (FixedLoops are not)
			pure ([],(!get, (M_Loop l)),t)
		tagList' ((M_FixedLoop l)::t) = do 	-- Treat fixed loops as barriers until data dependency is worked out properly
			pure ([],(!get, (M_FixedLoop l)),t)
		tagList' (M_Input::t) = do
			pure ([],(!get, (M_Input)),t)
		tagList' (M_Output::t) = do
			pure ([],(!get, (M_Output)),t)
		tagList' (h::t) = do
			pos <- get
			(l, (off, bar), r) <- tagList' t
			pure ((pos, h)::l, (off,bar), r)

		tagList : List MIR -> (List (Int, MIR), (Int, MIR), List MIR)
		tagList l = runPure $ tagList' l
		
		collectByTag : List (Int, MIR) -> List (Int, MIR)
		collectByTag l = do
			let view = map (Prelude.Basics.fst {b=MIR}) l
			let indices = sort $ nub view
			foldl (++) [] (map (\x => filter (\t => fst t == x) l) indices)

		resolveBarriers : (List (Int, MIR), (Int, MIR), List MIR) -> List MIR
		resolveBarriers (fore, (off,barrier), aft) = do
			let collectedTags = collectByTag fore
			let resolveFore = concat $ map (\t => [M_Move (fst t), snd t, M_Move (-(fst t))]) collectedTags
			let resolveAft = case aft of [] => []; _ => (resolveBarriers . tagList) aft
			resolveFore ++ [M_Move off, barrier, M_Move (-off)]  ++ resolveAft

		performOpt : List MIR -> List MIR
		performOpt l = resolveBarriers ([], (0, M_Move 0), (M_Move 0)::l)--joinTaggedCodepoints $ collectByTag $ runPure $ tagList l
		
		innerOpt : MIR -> MIR
		innerOpt (M_Loop l) = M_Loop l
		innerOpt (M_FixedLoop l) = M_FixedLoop $ performOpt l
		innerOpt x = x

[removeNops] Opt List MIR 1 where
	optIR list = performOpt list where
		performOpt : List MIR -> List MIR
		performOpt ((M_Move 0)::t) = performOpt t
		performOpt ((M_Add 0)::t) = performOpt t
		performOpt (h::t) = h :: performOpt t
		performOpt [] = []

emitterMIR : Bits64 -> List MIR -> List Bits8
emitterMIR memAddr list = 
		case runJit (emitter list) of
			Left err => []
			Right jit => trace (show $ length $ mach jit) mach $ record { 
				mach = (([0x48,0xB8] ++ (b64ToBytes memAddr)) ++ (mach jit) ++ [0xC3]),
				memoff $= (+10)
			} jit
	where
	
	emitter : List MIR -> X86 ()
	emitter ((M_Move n)::t) = do
		add rax (I (prim__zextInt_B64 n))
		emitter t
	emitter ((M_Add n)::t) = do
		emit [0x80,0x00,n]	--add byte [rax], n
		emitter t
	emitter (M_Output::t) = do
		push rax
		mov rdi (I 1)
		mov rsi rax
		mov rdx (I 1)
		mov rax (I 1)
		syscall
		pop rax
		emitter t
	emitter (M_Input::t) = do
		push rax
		mov rdi (I 0)
		mov rsi rax
		mov rdx (I 1)
		mov rax (I 0)
		syscall
		pop rax
		emitter t
	emitter ((M_Set n)::t) = do
		emit [0xC6, 0x00, n]
		emitter t
	emitter ((M_MulAddOff k off)::t) = do
		{-mov rdx rax
		emit [0x48,0x8B,0x82] -- mov rax, [rdx + lit]
		imm32 $ prim__zextInt_B32 off
		imul rax (cast Bits32 k)
		emit [0x48, 0x89, 0x92]-- mov [rdx + lit], rax
		imm32 $ prim__zextInt_B32 off
		mov rax rdx-}
		
		emit [0x48, 0x6B, 0x90] -- imul rdx, [rax + dword lit1], byte lit2
		imm32 $ prim__zextInt_B32 off
		emit [k]
		emit [0x48,0x89,0x90] -- mov [rax + dword lit1], rdx
		imm32 $ prim__zextInt_B32 off

	emitter ((M_Loop l)::t) = do
		let inner = runJit $ emitter l
		case inner of
			Left err => raise err
			Right ijit => do
				emit [0x80,0x38,0x00] -- cmp byte [rax], 0x0
				emit [0x0F]
				emit [0x84]
				imm32 $ (prim__zextInt_B32 $ toIntNat $ length $ mach ijit)
				prevLbl <- label
				emit $ mach ijit
				emit [0x80,0x38,0x00]
				jnz prevLbl
		emitter t
	emitter ((M_FixedLoop l)::t) = do
		let inner = runJit $ emitter l
		case inner of
			Left err => raise err
			Right ijit => do
				emit [0x80,0x38,0x00] -- cmp byte [rax], 0x0
				emit [0x0F]
				emit [0x84]
				imm32 $ (prim__zextInt_B32 $ toIntNat $ length $ mach ijit)
				prevLbl <- label
				emit $ mach ijit
				emit [0x80,0x38,0x00]
				jnz prevLbl
		emitter t
	emitter [] = pure()

total
llirAsBF : LLIR -> String
llirAsBF LL_Left = "<"
llirAsBF LL_Right = ">"
llirAsBF LL_Inc = "+"
llirAsBF LL_Dec = "-"
llirAsBF LL_OpenLoop = "["
llirAsBF LL_CloseLoop = "]"
llirAsBF LL_Input = ","
llirAsBF LL_Output = "."

mutual
	mirAsBF : MIR -> String
	mirAsBF (M_Loop l) = assert_total $ "[" ++ toBF l ++ "]"
	mirAsBF (M_FixedLoop l) = assert_total $ "[" ++ toBF l ++ "]"
	mirAsBF M_Input = ","
	mirAsBF M_Output = "."
	mirAsBF (M_Add x) = let x = if x >= 0x80 then (prim__zextB8_Int x) - 256 else prim__zextB8_Int x in 
		case compare x 0 of
			GT => pack $ replicate (toNat x) '+'--with Strings (the String "+") ++ (mirAsBF (M_Add (with Interfaces  x-1)))
			LT => pack $ replicate (toNat (-x)) '-'
			EQ => ""
	mirAsBF (M_Move x) = case compare x 0 of
		GT => ">" ++ (mirAsBF (M_Move (x-1)))
		LT => "<" ++ (mirAsBF (M_Move (x+1)))
		EQ => ""
	mirAsBF (M_Set x) = assert_total $ "[-]" ++ mirAsBF (M_Add x)
	mirAsBF op = "ERR translating " ++ show op

	toBF : List MIR -> String
	toBF l = concat $ map mirAsBF l

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
