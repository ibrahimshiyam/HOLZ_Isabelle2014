PIZZASOURCES =  GenLexis.pizza

JAVACCSOURCES = Parser.jj

JAVACCOBJECTS = ParserConstants.java Parser.java ParserTokenManager.java \
                Token.java ASCII_UCodeESC_CharStream.java \
		ParseException.java TokenMgrError.java

all:
	$(JAVACC) Parser.jj && pc $(PIZZASOURCES) $(JAVACCOBJECTS)

clean:
	rm -f $(JAVACCOBJECTS)

