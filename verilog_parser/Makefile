.PHONY: all clean

all: Verilog/Test buildTree

Verilog/ErrM.hs Verilog/Lex.x Verilog/Print.hs Verilog/Par.y Verilog/Test.hs: Verilog.cf
	bnfc --haskell -d Verilog.cf

%.hs: %.y
	happy --ghc --coerce --array --info $<

%.hs: %.x
	alex --ghc $<

Verilog/Test: Verilog/Test.hs Verilog/ErrM.hs Verilog/Lex.hs Verilog/Par.hs Verilog/Print.hs
	ghc --make $< -o $@

buildTree: buildTree.hs Verilog/Test
	ghc -Wall -Wextra --make buildTree.hs

clean:
	rm -rf Verilog/
	rm -f buildTree buildTree.o buildTree.hi

translate: buildTree
	for f in test_cases/good/*.sv; do echo Translating good test $$f ... && ./buildTree --good $$f; done

	for f in test_cases/bad/*.sv; do echo Translating bad test $$f ... && ./buildTree --bad $$f; done
