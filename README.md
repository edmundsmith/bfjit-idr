##Intro

This is a basic JIT compiler for BrainF, written purely in Idris. Certain low-level features and activities (mmap, etc.) are provided by using FFI on the C stdlib, which appears to be included by default as a side-effect of Idris' compilation using C as an intermediate language.

This is also why I call `labs` on a pointer during the lifetime of the program (if this is run in kernel mode (thus with the high bit set), something has gone wrong).

##Overview:

* Assembly.idr - Implements an X86 assembly monad similar to the one in [Monads to Machine Code](http://www.stephendiehl.com/posts/monads_machine_code.html). It's a bit limited with different address and register stuff ATM, so I often drop down to emitting raw bytes rather than using the named instructions
* BF.idr - Contains the BF-specific stuff, like IR and opt passes. Also has the \*IR -> X86 () passes.
* JIT.idr - Contains the specifics for executing a buffer as a function, including allocating a tape buffer, mmapping and unmmapping the executable buffer and main reading the files to JIT. This also contains a custom `IOEff` Effect, a useful but overly-broad effect for all IO processes within effectful code which otherwise lack proper effects (eg. custom FFI functions, mmap). Most of these are single functions not worth writing effects for, so I've wrapped them into the IOEff with `performIO : IO () -> Eff () [IOEFF]` instead.
