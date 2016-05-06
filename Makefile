all:
	cd src; happy -gca ParEthver.y; cd ..
	cd src; alex -g LexEthver.x; cd ..
	cd src; ghc --make MakeEthver.hs -o ../MakeEthver; cd ..

clean:
	cd src; rm -f *.log *.aux *.hi *.o *.dvi; cd ..; rm MakeEthver

distclean: clean
	cd src; rm -f DocEthver.* LexEthver.* ParEthver.* LayoutEthver.* SkelEthver.* PrintEthver.* TestEthver.* AbsEthver.* TestEthver ErrM.* SharedString.* ComposOp.* ethver.dtd XMLEthver.* Makefile*; cd ..
	

