module Unlifter

%access public export

interface CompilationTarget c where
	targetName : String
	compilationType : Type

--interface CompilationTarget c => Unlift a c where
--	unlift : a -> compilationType

interface Interpreter prog env art | prog, env where
	step : env -> env
	initial : prog -> env
	terminated : env -> Bool
	artifact : (machine : env) -> 
		--{auto ok : terminated machine = True} -> 
		art

Interpreter (List (b -> b)) (List (b->b), b->b) (b->b) where
	step (h::t, f) = (t, h . f)
	step x = x
	initial l = (l, id)
	terminated ([],_) = True
	terminated _ = False
	artifact (_, f) = f

interpret : Interpreter p e a => p -> a
interpret program {p=pp} {e=ee} {a=aa} = interpret' program init where
	init : ee
	init = initial {prog=pp} {env=ee} {art=aa} program
	interpret' : pp -> ee -> aa
	interpret' program environ =
		case decEq (terminated {prog=pp} {env=ee} {art=aa} environ) True of
			Yes prf => artifact {prog=pp} {env=ee} {art=aa} environ
			No contra => interpret' program (the ee (step {prog=pp} {env=ee} {art=aa} environ))