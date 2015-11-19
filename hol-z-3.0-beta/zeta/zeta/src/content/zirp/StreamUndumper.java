// {[(




/* ****************************************************************** */
/* ****************************************************************** */
/* **								   ** */
/* ** Undumping ascii strings into Java abstract syntax            ** */
/* **								   ** */
/* ** (c) Dong Yang, Jochen Burghardt, GMD FIRST, 1997		   ** */
/* **								   ** */
/* ****************************************************************** */
/* ****************************************************************** */



package zeta.content.zirp;

import zeta.util.*;
import zeta.content.zirp.*;
import java.io.*; 
import java.lang.reflect.*; 
import java.util.*; 





/** This class implements an input stream that has additional methods
    for undumping / parsing into Java abstract syntax of mSZ.
    @see zeta.content.zirp.StreamDumper */
public class StreamUndumper extends StreamTokenizer {



/* ****************************************************************** */
/* ***** constants ************************************************** */
/* ****************************************************************** */



/** string representation of end-of-file token */
final public static String T_EOF = "<**EOF**>";

/** string representation of end-of-line token */
final public static String T_EOL = "\n";



/* ****************************************************************** */
/* ***** public variables ******************************************* */
/* ****************************************************************** */



/** for internal test purposes only */
public boolean debug = true;

/** output stream for error messages */
public PrintStream err = System.err;

public boolean supportLatex = true;

public boolean unquoteStrings = false;

public boolean supportEscapes = false;

public boolean supportEndIndicator = false;

public String endIndicator = "@end@";

public boolean supportTickIndicator = false;

public String tickIndicator = "@tick@";

public int maxErr = 100;

private int errCnt;



/* ****************************************************************** */
/* ***** private variables ****************************************** */
/* ****************************************************************** */



/** string to be prepended to external names to obtain class names */
private String prefix;

/** ring buffer of recent input history */
private String [] lastTokens = new String[64];

/** token count, first token = 0 */
private int tokenCnt;

/** token count where last error was reported */
private int lastErrorAt = -1;

/** true if history buffer has not been modified 
    since last error output */
private int tokensShownAt;

private InputStream rawIn;



/* ****************************************************************** */
/* ***** constructors *********************************************** */
/* ****************************************************************** */



/** Creates a StreamUndumper that reads from the specified input 
    stream.
    @param in input stream
    @param pr string to be prepended to external names 
	     to obtain class names */
public StreamUndumper(InputStream in,String pr) {
    super(in);
    rawIn = in;
    ordinaryChar('/');
    ordinaryChar('.');
    ordinaryChar('-');
    wordChars('$','$');
    wordChars('_','_');
    ordinaryChars('0','9');
    wordChars('0','9');
    prefix = (pr == null ? "" : pr);
    resetErrors();
}


public StreamUndumper(InputStream i)		{this(i,"");}
public StreamUndumper(String p)			{this(System.in,p);}
public StreamUndumper()				{this(System.in,"");}



public void close() throws IOException {
    rawIn.close();
}



/* ****************************************************************** */
/* ***** scanner **************************************************** */
/* ****************************************************************** */



/** consider all chars from <CODE>s</CODE> as word chars */
public void makeWordChars(String s) {
    if (s != null)
	for (int i=0; i<s.length(); ++i)
	    wordChars(s.charAt(i),s.charAt(i));
}



/** convert current token into string */
public String ttstring() {
    switch (ttype) {
    case TT_EOF:
	return T_EOF;
    case TT_WORD:
	return sval;
    case TT_EOL:
	return T_EOL;
    case TT_NUMBER:
	return "" + nval;
    case '"':
	return trString(sval);
    default:
	return "" + ((char)(ttype));
    }
}



/** convert current token into a string, 
    adding quotes for string tokens */
public String ttqstring() {
    switch (ttype) {
    case TT_EOF:
	return T_EOF;
    case TT_WORD:
	return sval;
    case TT_EOL:
	return T_EOL;
    case TT_NUMBER:
	return "" + nval;
    case '"':
	return "\"" + trString(sval) + "\"";
    default:
	return "" + ((char)(ttype));
    }
}



/** add escape chars to <CODE>in</CODE> such that the result would be
    scanned as <CODE>in</CODE> again,
    " and \ are escaped as \" and \\ , respectively */

/*
public String addEscapes(String in) {
    char [] out = new char[in.length()*2+1];
    int o = 0;
    for (int i=0; i<in.length(); ++i) {
	char inI = in.charAt(i);
	if (inI == '"' || inI == '\\')
	    out[o++] = '\\';
	out[o++] = inI;
    }
    return new String(out,0,o);
}
*/



/** add escape chars to <CODE>in</CODE> such that the result would be
    scanned as <CODE>in</CODE> again,
    NL, " and \ are escaped as \n, \" and \\ , respectively */
public String addEscapes(String in) {
    char [] out = new char[in.length()*2+1];
    int o = 0;
    for (int i=0; i<in.length(); ++i) {
	char inI = in.charAt(i);
	if (inI == '"' || inI == '\\') {
	    out[o++] = '\\';
	    out[o++] = inI;
	} else if (inI == '\n') {
	    out[o++] = '\\';
	    out[o++] = 'n';
	} else {
	    out[o++] = inI;
	}
    }
    return new String(out,0,o);
}





/** reverse the effect of addEscapes */
public String removeEscapes(String in) {
    char [] out = new char[in.length()+1];
    int o = 0;
    boolean esc = false;
    for (int i=0; i<in.length(); ++i) {
	char inI = in.charAt(i);
	if (esc) {
	    if (inI != '\\' && inI != '"')
		out[o++] = '\\';
	    out[o++] = inI;
	    esc = false;
	} else if (in.charAt(i) == '\\') {
	    esc = true;
	} else {
	    out[o++] = inI;
	}
    }
    if (esc)
	out[o++] = '\\';
    return new String(out,0,o);
}



private char specialToLatex(char c1,char c2) {
    //if (c1 == 'D' && c2 == 'S')	return '\'';
    if (c1 == 'E' && c2 == 'M')	return '!';
    if (c1 == 'H' && c2 == 'M')	return '#';
    if (c1 == 'S' && c2 == 'T')	return '*';
    if (c1 == 'P' && c2 == 'L')	return '+';
    if (c1 == 'M' && c2 == 'N')	return '-';
    if (c1 == 'D' && c2 == 'T')	return '.';
    if (c1 == 'C' && c2 == 'O')	return ':';
    if (c1 == 'L' && c2 == 'T')	return '<';
    if (c1 == 'E' && c2 == 'Q')	return '=';
    if (c1 == 'G' && c2 == 'T')	return '>';
    if (c1 == 'Q' && c2 == 'M')	return '?';
    if (c1 == 'B' && c2 == 'S')	return '\\';
    if (c1 == 'U' && c2 == 'S')	return '_';
    error("specialToLatex('" + c1 + "','" + c2 + "')");
    return ' ';
}



/** convert Isabelle repr of strings to LaTeX repr */
public String convToLatex(String in) {
    if (in == null || in.length() == 0)
	return in;
    char [] out = new char[in.length()+1];
    int o = 0;
    for (int i=0; i<in.length(); ) {
	if (i+2 < in.length() && in.charAt(i+2) == '_') {
	    char c = specialToLatex(in.charAt(i),in.charAt(i+1));
	    if (c != ' ') {
		out[o++] = c;
		i += 3;
	    } else {
		out[o++] = in.charAt(i++);
		out[o++] = in.charAt(i++);
		out[o++] = in.charAt(i++);
	    }
	} else {
	    out[o++] = in.charAt(i++);
	}
    }
    return new String(out,0,o);
}



public String unquote(String in) {
    int lgth;
    if (in == null)
	return in;
    lgth = in.length();
    if (lgth < 2)
	return in;
    else if (in.charAt(0) == '"' && in.charAt(lgth-1) == '"')
	return in.substring(1,lgth-1);
    else
	return in;
}



public String trString(String in) {
    if (in == null)
	return null;
/*db**    w("trString < '" + in + "'");				**de*/
    if (supportLatex)
	in = convToLatex(in);
    if (unquoteStrings)
	in = unquote(in);
    if (supportEscapes)
	in = addEscapes(in);
/*db**    w("trString > '" + in + "'");				**de*/
    return in;
}



/** advance input to next token */
public int nextToken() throws IOException {
    int tk = super.nextToken();
    ++tokenCnt;
/*db**    w("token "+tokenCnt+" = "+tk+" <"+ttstring()+">");	**de*/
    lastTokens[tokenCnt % 64] = ttqstring();
    if (   supportEndIndicator
	&& endIndicator != null 
	&& endIndicator.equals(ttstring())
        || supportTickIndicator
	&& tickIndicator != null 
	&& tickIndicator.equals(ttstring())) {
	pushBack();
	throw (new IOException(ttstring()));
    } else {
	return tk;
    }
}



/** skip back input to previous token */
public void pushBack() {
    super.pushBack();
    lastTokens[tokenCnt % 64] = "";
    --tokenCnt;
}



/** ignore input tokens until <CODE>stop</CODE> occurs */
public void skipTo(String stop) throws IOException {
/*db**    b("skipTo " + stop);					**de*/
    while (! stop.equals(ttstring()) && ttype != TT_EOF)
	nextToken();
/*db**    e("skipTo");						**de*/
}



/** succeed iff current input token equals <CODE>expect</CODE> */
public boolean scan(String expect) throws IOException {
    nextToken();
    if (expect.equals(ttstring())) {
	return true;
    } else if (ttype != TT_EOF) {
	pushBack();
	return false;
    } else {
	throw new IOException("scan <" + expect + "> at EOF");
    }
}



/** report an error and skip if current input token does not equal 
    <CODE>expect</CODE> */
public void force(String expect) throws IOException {
    nextToken();
    if (!expect.equals(ttstring())) {
	error("expected <" + expect + ">");
	if (ttype == TT_EOF)
	    throw new IOException("force <" + expect + "> at EOF");
    }
}



/** report an error and skip if current input token does not equal
    <CODE>endIndicator</CODE> */
public void forceEnd() throws IOException {
    if (endIndicator == null)
	return;
    boolean save = supportEndIndicator;
    supportEndIndicator = false;
    force(endIndicator);
    supportEndIndicator = save;
}



/** report an error and skip if current input token does not equal
    <CODE>tickIndicator</CODE> */
public String forceTick() throws IOException {
    if (tickIndicator == null)
	return null;
    boolean save = supportTickIndicator;
    supportTickIndicator = false;
    force(tickIndicator);
    supportTickIndicator = save;
    if (! tickIndicator.equals(ttstring()))
	return null;
    nextToken();
    return ttstring();
}



public int available() throws IOException {
    int a = rawIn.available();
/*db**    w("available " + rawIn + " = " + a);			**de*/
    return a;
}



/** report an error */
public void error(String msg) {
    if (tokenCnt == lastErrorAt)
	return;
    lastErrorAt = tokenCnt;
    ++errCnt;
    if (errCnt > maxErr)
	return;
    err.println("\nStreamUndumper error in line " + lineno()
		    + " at token " + tokenCnt 
		    + " <" + ttstring() + ">:\n" + msg); 
    if (tokensShownAt < tokenCnt - 64) {
	err.println("last tokens read:");
	for (int i=1; i<=64; ++i) {
	    String tok = lastTokens[(tokenCnt+i) % 64];
	    if (tok.length() > 0)
		err.print(" " + tok);
	}
	err.println("");
	tokensShownAt = tokenCnt;
    }
}



public void resetErrors() {
    for (int i=0; i<64; ++i)
	lastTokens[i] = "";
    tokenCnt = -1;
    tokensShownAt = Integer.MIN_VALUE;
    errCnt = 0;
}



/* ****************************************************************** */
/* ***** undumping Ascii to Java abstract syntax ******************** */
/* ****************************************************************** */



/** conv input term into Java object of class <CODE>expected</CODE> */
public Object undump(Class expect) throws IOException {
/*db**    b("undump " + expect.getName());			**de*/
    if (scan("Name")) {
	nextToken();
/*db**	e("undump Name " + ttstring());				**de*/
	return new Name(ttstring());
    } else if (scan("Decorate")) {
	nextToken();
	Object res = new Expr.UnaryKind.Decorate(ttstring());
/*db**	e("undump " + res);					**de*/
	return res;
    } else if (scan("Number")) {
	nextToken();
/*db**	e("undump Number " + ttstring());			**de*/
	return new Expr.Number(ttstring());
    } else if (scan("Other")) {
	nextToken();
/*db**	e("undump Other " + ttstring());			**de*/
	return makeOther(expect,ttstring());

    } else if (scan("List")) {
	force("[");
	Vector argsV = new Vector();
	Class expectI = expect.getComponentType();
	while (! scan("]")) {
	    Object o = undump(expectI);
	    if (o == null)
		break;
	    argsV.addElement(o);
	    scan(",");
	}
	Object res;
	try {
	    res = Array.newInstance(expectI,argsV.size());
	}
	catch (IllegalArgumentException e) {
	    error("undump List [" + argsV.size() + "], expected "
			    + expectI.getName());
/*db**	    e("undump x2");					**de*/
	    return null;
	}
	for (int i=0; i<argsV.size(); i++)
	    try {
		Array.set(res,i,argsV.elementAt(i));
	    } 
	    catch (IllegalArgumentException e) {
		error("undump List "
			+ expectI.getName()
			+ " elem " + i + ": " 
			+ argsV.elementAt(i).getClass().getName());
/*db**		e("undump x1");					**de*/
		return null;
	    }
/*db**	e("undump " + res);					**de*/
	return res;
    } else if (ttype == '"') {
	nextToken();
	String rd = ttstring();
	String ex = expect.getName();
	String eP = ex.substring(ex.lastIndexOf(".")+1,ex.length());
	       eP = eP.substring(eP.lastIndexOf("$")+1,eP.length());
	String nm = (rd.equals(eP) ? ex : ex+"$"+rd);
/*db**	w("rd = <" + rd + ">");					**de*/
/*db**	w("ex = <" + ex + ">");					**de*/
/*db**	w("nm = <" + nm + ">");					**de*/
	force("$$");
	force("[");
	Object res;
	try {
	    res = makeClass(nm);
	}
	catch (ClassNotFoundException e) {
/*db**	    w("caught intended excp " + e);			**de*/
	    res = makePrimitive(expect.getDeclaredFields(),rd,ex);
	}
	force("]");
/*db**	e("undump " + res);					**de*/
	return res;
    } else {
	error("illegal token " + ttstring());
/*db**	e("undump (illegal token)" + ttstring());		**de*/
	return null;
    }
}



/** build Java object of class <CODE>Other</CODE> */
private Object makeOther(Class expect,String value) {
    try {
/*db**	b("makeOther " + expect.getName() + "," + value);	**de*/
	String name = expect.getName() + "$Other";
	Class cl = Class.forName(name);
	Constructor [] crs = cl.getConstructors();
	if (crs.length != 1)
	    error("too many constructors for class <" + name + ">");
	String [] argsO = {value};
/*db**	e("makeOther");						**de*/
	return crs[0].newInstance(argsO);
    }
    catch (Exception e) {
	error("makeOther:\n" + e);
	return null;
    }
}



/** build Java object of composed class named <CODE>name</CODE>,
    read terms and undump to field values */
private Object makeClass(String name) 
			    throws ClassNotFoundException, IOException {
    try {
/*db**	b("makeClass " + name);					**de*/
	Class cl = Class.forName(name);
	Constructor [] crs = cl.getConstructors();
	if (crs.length != 1)
	    error("too many constructors for class <" + name + ">");
	Class [] crArgs = crs[0].getParameterTypes();
	Vector argsV = new Vector();  
	for (int k=0; k<crArgs.length; ++k) {
	    argsV.addElement(undump(crArgs[k]));
	    if (k < crArgs.length-1)
		force(",");
	}
	Object [] argsO = new Object[argsV.size()];
	argsV.copyInto(argsO);
	Object res;
	try {
	    res = crs[0].newInstance(argsO);
	} 
	catch (IllegalArgumentException e) {
	    error("makeClass " + name + ":\n" + e);
/*db**	    e("makeClass " + e);				**de*/
	    return null;
	}
/*db**	e("makeClass");						**de*/
	return res;
    }
    catch (InvocationTargetException e) {
	error("makeClass:\n" + e);
/*db**	e("makeClass " + e);					**de*/
	return null;
    }
    catch (InstantiationException e) {
	error("makeClass:\n" + e);
/*db**	e("makeClass " + e);					**de*/
	return null;
    }
    catch (IllegalAccessException e) {
	error("makeClass:\n" + e);
/*db**	e("makeClass " + e);					**de*/
	return null;
    }
}



/** return the Java constant named <CODE>name</CODE> from 
    <CODE>fields</CODE> */
private Object makePrimitive(Field [] fields,String name,String ex) {
    try {
/*db**	b("makePrimitive " + name);				**de*/
	for (int i=0; i<fields.length; ++i) {
/*db**	    w("field " + i + " = " + fields[i].getName());	**de*/
	    if (name.equals(fields[i].getName())) {
/*db**		e("makePrimitive " + fields[i].getName());	**de*/
		return fields[i].get(null);
	    }
	}
	error("makePrimitive: " + name + " not found in " + ex);
/*db**	e("makePrimitive (not found)");				**de*/
	return null;
    }
    catch (IllegalAccessException e) {
	error("makePrimitive:\n" + e);
/*db**	e("makePrimitive " + e);				**de*/
	return null;
    }
    catch (IllegalArgumentException e) {
	error("makePrimitive:\n" + e);
/*db**	e("makePrimitive " + e);				**de*/
	return null;
    }
}



/* ****************************************************************** */
/* ***** debugging ************************************************** */
/* ****************************************************************** */



String indent = "";



/** write debug output */
void w(String s) {
    if (debug)
	err.println(indent + "SU " + s);
}



/** method begin */
void b(String s) {
    w(">" + s);
    indent += "  ";
}



/** method end */
void e(String s) {
    indent = indent.substring(2);
    w("<" + s);
}





}





// )]}


