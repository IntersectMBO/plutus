MHSDIR=..
BIN=../bin
TOOLS=../Tools

# Generate combinator file
blinky.c:	Blinky.hs $(BIN)/Addcombs $(BIN)/mhseval $(BIN)/mhs
	MHSDIR=$(MHSDIR) $(BIN)/mhs -i$(LIB) Blinky -oBlinky.comb
	$(BIN)/mhseval +RTS -rBlinky.comb -oBlinky-opt.comb
	$(BIN)/Addcombs Blinky-opt.comb blinky.c

$(BIN)/Addcombs:	$(TOOLS)/Addcombs.hs $(BIN)/mhs
	MHSDIR=$(MHSDIR) $(BIN)/mhs -i$(TOOLS) Addcombs -o$(BIN)/Addcombs

# To compile for STM32 the following files are needed:
#  src/runtime/bfile.c
#  src/runtime/config-stm32f4.h
#  src/runtime/eval-stm32f.c
#  src/runtime/eval.c
#  blinky.c
# The Keil project should include
#  eval-stm32f.c
#  blinky.c
# To get enough memory I modified startup_stm32f407xx.s
#   Stack_Size      EQU     0x00008000
#   Heap_Size       EQU     0x0000E000
# These values are not optimized, they just happen to work
# for this project.
