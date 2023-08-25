O		?= x86_64
CLANGPATH	?= "/usr/lib/llvm-5.0/bin/"
CFLAGS		+= -fno-PIE
CFLAGS		+= -ffreestanding -MD -MP
CFLAGS		+= -Wall
CFLAGS		+= -g
CFLAGS		+= -mno-red-zone
CFLAGS		+= -mno-sse -mno-mmx -mno-sse2 -mno-3dnow -mno-avx
# CFLAGS       += -DCOMMIT_HASH=$(shell git rev-parse --short --verify HEAD)
# CFLAGS       += -DCOMMIT_BRANCH=$(shell git rev-parse --abbrev-ref --verify HEAD)
CFLAGS		+= -I include -I $(O)/include
NR_CPUS		= 1
MKDIR_P		:= mkdir -p

KERNEL_CFLAGS = $(CFLAGS) -DNR_CPUS=$(NR_CPUS) -fwrapv -I include

LLS		:=		\
		$(O)/scm.ll	\

# generate .ll from .c
$(O)/%.ll: %.c
	$(MKDIR_P) $(@D)
	$(CLANGPATH)clang -o $@~ -c -S -emit-llvm $(KERNEL_CFLAGS) -O2 $<
	./script/no_undef.sh $@~
	mv $@~ $@
	@echo 'convert .c --> .ll done!'	

$(O)/%.py: $(O)/%.ll
	$(Q)$(MKDIR_P) $(@D)
	@touch $(join $(dir $@), __init__.py)
	./irpy "$<" > "$@"
	@echo 'convert .ll --> $@ done!'
	
all: $(LLS) $(O)/scm.py
	cp ./main.py ./specs.py ./irpy ./$(O)
	cp ./datatype -rf ./$(O)
	cp ./libirpy -rf ./$(O) 
	cp ./invariants.py ./$(O)
	cp ./head.py ./$(O)
	cp ./equiv.py ./$(O)
	@echo 'copy files to build dir done!'

verify:
#	cp ./specs.py ./$(O)
	python2 $(O)/main.py
	@echo 'executing test case done!'
	

app: 
	llvm-as-5.0 $(O)/TIPC.ll -o TIPC.bc
	lli-5.0 TIPC.bc
#	$(CLANGPATH)clang -c counter.c -o counter.o
#	$(CLANGPATH)clang -o counter counter.o

clean:
	rm -rf $(O)

