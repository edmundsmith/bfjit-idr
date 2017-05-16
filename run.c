#include "stdlib.h"
#include "run.h"
#include <sys/mman.h>
int run(int (*f)(int)) { return f(0); }
int make_exe(void* p) { return mprotect(p, 1, PROT_READ|PROT_EXEC); }

const int idr_PROT_EXEC = PROT_EXEC;
const int idr_PROT_READ = PROT_READ;
const int idr_PROT_WRITE = PROT_WRITE;
const int idr_PROT_NONE = PROT_NONE;

const int idr_MAP_SHARED = MAP_SHARED;
const int idr_MAP_PRIVATE = MAP_PRIVATE;
const int idr_MAP_ANONYMOUS = MAP_ANONYMOUS;

void * run_mmap(void *addr, size_t length, int prot, int flags,
           int fd, off_t offset)
{
	void* p = mmap(addr, length, prot, flags, fd, offset);
	printf("%d %d %d %d\n", idr_PROT_NONE, idr_PROT_WRITE, idr_PROT_READ, idr_PROT_EXEC);
	printf("%p\n", p);
	return p;
}
int run_munmap(void *addr, size_t length)
{
	return munmap(addr, length);
}
