// {[(





/* ****************************************************************** */
/* ****************************************************************** */
/* **                                                              ** */
/* ** Ascii dumping of Java abstract syntax                        ** */
/* **                                                              ** */
/* ** (c) Dong Yang, Jochen Burghardt, GMD FIRST, 1997             ** */
/* **                                                              ** */
/* ****************************************************************** */
/* ****************************************************************** */



package zeta.content.zirp;

import zeta.util.*;
import zeta.content.zirp.*;
import java.io.*;
import java.lang.reflect.*;
import java.util.*;





/** This class implements an output stream that has additional methods 
    for Ascii dumping of Java abstract syntax of mSZ.
    @see zeta.content.zirp.StreamUndumper */
public class StreamDumper extends PrintStream {



/* ****************************************************************** */
/* ***** public variables ******************************************* */
/* ****************************************************************** */



/** approximate max line length of output (default 64);
    if 0, dont restrict output line length */
public int lineLgth = 64;

/** for internal test purposes only */
public boolean debug = true;

/** output stream for error messages */
public PrintStream err = System.err;

public boolean supportLatex = true;
public boolean supportEscapes = true;

public boolean unquoteStrings = true;

/** include term annotations into dump */
public boolean dumpAnnotations = true;

/** precede each annotation slot by its name */
public boolean dumpSlotNames = true;

/** dump all slots by default */
public boolean dumpAllSlots = true;



/* ****************************************************************** */
/* ***** private variables ****************************************** */
/* ****************************************************************** */



/** current output column */
private int col = 0;

Class ClassString;
Class ArrayString;
Class ClassTerm;
Class ArrayTerm;

BitSet exceptionalSlots = new BitSet(64);



/* ****************************************************************** */
/* ***** constructors *********************************************** */
/* ****************************************************************** */



/* BufferedOutPutStream beschleuningt um Faktor 2 ??? */

/** Create a StreamDumper that writes to the specified output stream.
    @param o output stream */
public StreamDumper(OutputStream o) {
    super(o);
    try {
	ClassString = Class.forName(  "java.lang.String");
	ArrayString = Class.forName("[Ljava.lang.String;");
	ClassTerm   = Class.forName(  "zeta.util.Term");
	ArrayTerm   = Class.forName("[Lzeta.util.Term;");
/*db**	w("StreamDumper(" + o + ")");				**de*/
/*db**	w("ClassString=" + ClassString);			**de*/
/*db**	w("ArrayString=" + ArrayString);			**de*/
/*db**	w("ClassTerm=" + ClassTerm);				**de*/
/*db**	w("ArrayTerm=" + ArrayTerm);				**de*/
    }
    catch (ClassNotFoundException e) {
	error("cant initialize annotation types: " + e);
    }
}



/** Create a StreamDumper that writes to System.out  */
public StreamDumper() {
    this(System.out); 
}



/* ****************************************************************** */
/* ***** length-restricted printing ********************************* */
/* ****************************************************************** */



/** print String <CODE>s</CODE> */
public void print(String s) {
    if (lineLgth > 0 && col >= lineLgth) {
	super.println();
	col = 0;
    }
    super.print(s);
    col += s.length();
}



/** print String <CODE>s</CODE> followed by newline */
public void println(String s) {
    if (lineLgth > 0 && col >= lineLgth)
	super.println();
    super.println(s);
    col = 0;
}



/* ****************************************************************** */
/* ***** escape characters ****************************************** */
/* ****************************************************************** */



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



/** convert LaTeX repr of strings to Isabelle repr */
public String convFromLatex(String in) {
    if (in == null || in.length() == 0)
	return in;
    char [] out = new char[in.length()*3+3];
    int o = 0;
    String app;
    for (int i=0; i<in.length(); ++i) {
	switch (in.charAt(i)) {
	//case '\'':	app = "DS";	break;
	case '!':	app = "EM";	break;
	case '#':	app = "HM";	break;
	case '*':	app = "ST";	break;
	case '+':	app = "PL";	break;
	case '-':	app = "MN";	break;
	case '.':	app = "DT";	break;
	case ':':	app = "CO";	break;
	case '<':	app = "LT";	break;
	case '=':	app = "EQ";	break;
	case '>':	app = "GT";	break;
	case '?':	app = "QM";	break;
	case '\\':	app = "BS";	break;
	case '_':	app = "US";	break;

	default:	app = "";	break;
	}
	if (app.length() == 0) {
	    out[o++] = in.charAt(i);
	} else {
	    for (int a=0; a<app.length(); ++a)
		out[o++] = app.charAt(a);
	    out[o++] = '_';
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
	in = convFromLatex(in);
    if (unquoteStrings)
	in = unquote(in);
    if (supportEscapes)
	in = addEscapes(in);
/*db**    w("trString > '" + in + "'");				**de*/
    return in;
}



/* ****************************************************************** */
/* ***** buffer flushing (neccessary for pipelines) ***************** */
/* ****************************************************************** */



private static final String flushString =
"                                                                      ";
private static final int flushLgth = flushString.length();



/** flush buffer by sending at least <CODE>n</CODE> layout chars */
public void flushBuffer(int n) {
    for (int i=0; i<n; i+=flushLgth)
	print(flushString);
    flush();
    flush();
}



/* ****************************************************************** */
/* ***** annotations ************************************************ */
/* ****************************************************************** */



/** mark this slot as exception from default
    @see dumpAllSlots */
public void addExceptionSlot(int s) {
    exceptionalSlots.set(s);
/*db**    w("addExceptionSlot(" + s + ")");			**de*/
}



/** mark this slot as exception from default
    @see dumpAllSlots */
public void addExceptionSlot(Slot s) {
    addExceptionSlot(s.getIndex());
}



/** mark this slot as exception from default
    @see dumpAllSlots */
public void addExceptionSlot(String name,Class type) {
    try {
	addExceptionSlot(Slot.register(name,type));
    }
    catch (Exception e) {
	error("addExceptionSlot " +name +"," +type.getName() +": " +e);
    }
}



/** mark this slot as exception from default
    @see dumpAllSlots */
public void addExceptionSlot(String name,String type) {
    try {
	addExceptionSlot(name,Class.forName(type));
    }
    catch (Exception e) {
	error("addExceptionSlot " + name + "," + type + ": " + e);
    }
}



/** mark this slot as exception from default
    @see dumpAllSlots */
public void addExceptionSlot(String type) {
    addExceptionSlot(type,type);
}



/** dump all slots of annotated term <CODE>object</CODE> */
private void dumpSlots(Object object) {
    try {
	Annotation an = ((AnnotatedTerm)(object)).an;
	Slot [] slots = an.getProvidedSlots();
	boolean first = true;
	for (int i=0; i<slots.length; ++i) {
	    Class slotType = slots[i].getType();
	    Object obj = slots[i].get(an);
/*db**	    w("slot " + slots[i].getName() + " : " 		**de*/
/*db**			+ slots[i].getType().getName());	**de*/
	    if (obj == null) {
/*db**		w("null annotation");				**de*/
		continue;
	    }
	    if (exceptionalSlots.get(slots[i].getIndex())==dumpAllSlots){
/*db**		w("slot " + slots[i].getIndex() + " excluded");	**de*/
		continue;
	    }
	    if (   ClassString.isAssignableFrom(slotType)
	        || ArrayString.isAssignableFrom(slotType)
		|| ClassTerm  .isAssignableFrom(slotType)
		|| ArrayTerm  .isAssignableFrom(slotType)) {
		if (first)
		    print(" ## [");
		else
		    print(",");
		if (dumpSlotNames)
		    print("\"" + slots[i].getName() + "\" $$ [");
		dump(obj);
		first = false;
		if (dumpSlotNames)
		    print("]");
	    } else {
/*db**		w("wrong type");				**de*/
	    }
	}
	if (!first)
	    print("]");

    }
    catch (ClassCastException e) {
	/* no AnnotatedTerm: do nothing */
    }
}



/* ****************************************************************** */
/* ***** dumping Java abstract syntax to Ascii ********************** */
/* ****************************************************************** */



/** convert Java <CODE>object</CODE> into output term */
public void dump(Object object) {
    if (object == null) {
	error("attempt to dump null object");
	print("<**dump:NULL**>");
	return;
    }
/*db**    b("dump " + object);					**de*/
    String full = object.getClass().getName();
    String name;
    name = full.substring(full.lastIndexOf(".")+1,full.length());
    name = name.substring(name.lastIndexOf("$")+1,name.length());
/*db**    w("full " + full + ", name " + name);			**de*/
    if (name.equals("Name")) {
	print("Name \"" + trString(((Name)(object)).getRepr()) + "\"");
    } else if (name.equals("Decorate")) {
	print("Decorate \"" 
		+ trString(((Expr.UnaryKind.Decorate)(object)).decore)
		+ "\"");
    } else if (name.equals("Number")) {
	print("Number \"" + ((Expr.Number)(object)).value + "\"");
    } else if (name.equals("Integer")) {
	print("Number \"" + ((Integer)(object)).intValue() + "\"");
    } else if (name.equals("Boolean")) {
	print("\"Boolean\" $$ []");
    } else if (name.equals("Other")) {
	Field [] fields = object.getClass().getDeclaredFields();
	if (fields.length != 1) {
	    error("too many fields in " + object.getClass().getName());
	    print("<**" + object.getClass().getName() + " has "
					+ fields.length + " fields**>");
	} else {
	    String s;
	    try { s = (String)(fields[0].get(object)); }
	    catch (IllegalAccessException e) {
		error(object.getClass().getName() + ".value: " + e);
		s = "<**" + object.getClass().getName() + ".value: "
							    + e + "**>";
	    }
	    print("Other \"" + trString(s) + "\"");
	}

    /*
    } else if (name.equals("Inop")) {
	print("Inop \"" + ((Item.Fixity.Inop)(object)).prio + "\"");
    } else if (name.equals("Mixgen")) {
	print("Mixgen \"" + ((Item.Fixity.Mixgen)(object)).argc + "\"");
    } else if (name.equals("Mixrel")) {
	print("Mixrel \"" + ((Item.Fixity.Mixrel)(object)).argc + "\"");
    } else if (name.equals("Mixop")) {
	print("Mixop \"" + ((Item.Fixity.Mixop)(object)).argc + "\"");
    */

    } else if (name.equals("String")) {
	print("String \"" + trString(object.toString()) + "\"");
    } else if (object.getClass().isArray()) {
	print("List [");
	for (int m=0; m<Array.getLength(object); ++m) {
	    if (m > 0)
		print(",");
	    dump(Array.get(object,m));
	}
	print("]");
    } else {
	Field [] fields = object.getClass().getDeclaredFields();
	String primName = getPrimitiveName(fields,object);
	if (primName != null) {
	    print("\"" + primName + "\" $$ []");
	} else {
	    print("\"" + name + "\" $$ [");
	    boolean first = true;
	    for (int i=0; i<fields.length; i++) {
		if (   fields[i].getType().getName().endsWith("Slot")
		    || fields[i].getName().equals("document")
		    || fields[i].getName().equals("region"))
		    continue;
		if (! first)
		    print(",");
		try {
		    dump(fields[i].get(object));
		    first = false;
		}
		catch (IllegalAccessException e) {
		    error(fields[i].getName() + ".get("+object+"): "+e);
		    print("<**" + fields[i].getName()
				+ ".get(" + object + "): " + e + "**>");
		}
	    }
	    if (dumpAnnotations) {
		dumpSlots(object);

	    }
	    print("]");
	}
    }
/*db**    e("dump");						**de*/
}



private final static int modFPS =   Modifier.FINAL
			  	  | Modifier.PUBLIC
			  	  | Modifier.STATIC;

private final static int modP = Modifier.PUBLIC;



/** return the name of the field of <CODE>fields</CODE> that equals 
    <CODE>object</CODE> */
private String getPrimitiveName(Field [] fields,Object object) {
/*db**    b("getPrimitiveName " + object);			**de*/
    int n = fields.length;
    String [] fieldTypeName = new String[n];
    for (int i=0; i<n; ++i)
	fieldTypeName[i] = fields[i].getType().getName();

/*db**for (int i=0; i<n; ++i)					**de*/
/*db**	w("getPrimitiveName i:" + i				**de*/
/*db**	    + ", name " + fields[i].getName()			**de*/
/*db**	    + ", type " + fieldTypeName[i]			**de*/
/*db**	    + ", mods " + Modifier.toString(			**de*/
/*db**			fields[i].getType().getModifiers()));	**de*/

    try {
	Field tagFld = null;
	int   tagVal = -1;
	for (int i=0; i<n; ++i)
	    if (   fieldTypeName[i].equals("int")
		&& fields[i].getName().endsWith("$$tag")) {
		tagFld = fields[i];
		tagVal = tagFld.getInt(object);
/*db**		w("getPrimitiveName i=" + i + " tv=" + tagVal);	**de*/
		break;
	    }
	if (tagFld == null) {
/*db**	    e("getPrimitiveName (no tag)");			**de*/
	    return null;
	}

	String objTypeName = object.getClass().getName();
	for (int i=0; i<n; ++i)
	    if (   fieldTypeName[i].equals(objTypeName)
		&& tagFld.getInt(fields[i].get(object)) == tagVal) {
/*db**		    e("getPrimitiveName " + i + ":"		**de*/
/*db**				+ fields[i].getName());		**de*/
		    return fields[i].getName();
	    }
/*db**	e("getPrimitiveName (tag not found)");			**de*/
	return null;

    }
    catch (IllegalAccessException e) {
/*db**	e("getPrimitiveName excp:" + e);			**de*/
	error(object.getClass().getName() + ": " + e);
	return "<**" + e + ":" + object.getClass().getName() + "**>";
    }

}



/* ****************************************************************** */
/* ***** errors ***************************************************** */
/* ****************************************************************** */



/** report an error */
public void error(String msg) {
    err.println("StreamDumper error: " + msg);
}



/* ****************************************************************** */
/* ***** debugging ************************************************** */
/* ****************************************************************** */



private String indent = "";



/** write debug output */
private void w(String s) {
    if (debug)
	err.println(indent + "SD " + s);
}



/** method begin */
private void b(String s) {
    w(">" + s);
    indent += "  ";
}



/** method end */
private void e(String s) {
    indent = indent.substring(2);
    w("<" + s);
}





}





// )]}


