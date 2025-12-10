

CUP = java_cup.Main
CUPFLAGS = -nopositions -expect 100

JLEX = JLex.Main

LATEX = latex
DVIPS = dvips
DVIPDF = dvipdfm


PARSER_BASEDIR=$(shell pwd)
PARSER_BINDIR=$(PARSER_BASEDIR)/bin


CLASSPATH:=$(CLASSPATH):$(PARSER_BASEDIR):$(JLEX_PATH)


all: parser.jar ap/parser/ApInput/Test.class


parser.jar: $(PARSER_BINDIR) $(PARSER_BINDIR)/ap/parser/ApInput/Absyn/ApInput.class $(PARSER_BINDIR)/ap/parser/ApInput/sym.class $(PARSER_BINDIR)/ap/parser/ApInput/Yylex.class $(PARSER_BINDIR)/ap/parser/ApInput/PrettyPrinter.class $(PARSER_BINDIR)/ap/parser/ApInput/parser.class
	cd $(PARSER_BINDIR) && jar cf $(PARSER_BASEDIR)/parser.jar ap/parser/ApInput


$(PARSER_BINDIR):
	mkdir $(PARSER_BINDIR)

clean:
#	rm -rf parser.jar
	rm -rf $(PARSER_BINDIR)
	rm -rf ap
	rm -rf ApInput.tex ApInput.dvi ApInput.aux ApInput.log ApInput.ps


# just any of the files that is created by bnfc
ApInput.tex: ApInput.cf
	bnfc -java1.5 -p ap.parser ApInput.cf

$(PARSER_BINDIR)/ap/parser/ApInput/Absyn/ApInput.java: ApInput.cf
	bnfc -java1.5 -p ap.parser ApInput.cf

$(PARSER_BINDIR)/ap/parser/ApInput/Absyn/ApInput.class: $(PARSER_BINDIR)/ap/parser/ApInput/Absyn/ApInput.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) ap/parser/ApInput/Absyn/*.java

ap/parser/ApInput/Yylex.java: ap/parser/ApInput/Yylex
	${JAVA} ${JAVA_FLAGS} ${JLEX} ap/parser/ApInput/Yylex

ap/parser/ApInput/sym.java ap/parser/ApInput/parser.java: ap/parser/ApInput/_cup.cup
	${JAVA} ${JAVA_FLAGS} ${CUP} ${CUPFLAGS} ap/parser/ApInput/_cup.cup
	mv sym.java parser.java ap/parser/ApInput/

$(PARSER_BINDIR)/ap/parser/ApInput/Yylex.class: ap/parser/ApInput/Yylex.java ap/parser/ApInput/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) ap/parser/ApInput/Yylex.java

$(PARSER_BINDIR)/ap/parser/ApInput/sym.class: ap/parser/ApInput/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) ap/parser/ApInput/sym.java

$(PARSER_BINDIR)/ap/parser/ApInput/parser.class: ap/parser/ApInput/parser.java ap/parser/ApInput/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) ap/parser/ApInput/parser.java

$(PARSER_BINDIR)/ap/parser/ApInput/PrettyPrinter.class: ap/parser/ApInput/PrettyPrinter.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) ap/parser/ApInput/PrettyPrinter.java

ap/parser/ApInput/Test.class: ap/parser/ApInput/Test.java $(PARSER_BINDIR)/ap/parser/ApInput/PrettyPrinter.class $(PARSER_BINDIR)/ap/parser/ApInput/Yylex.class $(PARSER_BINDIR)/ap/parser/ApInput/parser.class $(PARSER_BINDIR)/ap/parser/ApInput/sym.class
	${JAVAC} ${JAVAC_FLAGS} ap/parser/ApInput/Test.java

ApInput.dvi: ApInput.tex
	${LATEX} ApInput.tex

ApInput.pdf: ApInput.dvi
	${DVIPDF} ApInput.dvi

ApInput.ps: ApInput.dvi
	${DVIPS} ApInput.dvi -o ApInput.ps
