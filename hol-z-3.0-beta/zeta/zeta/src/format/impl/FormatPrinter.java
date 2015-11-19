package zeta.format.impl;

import java.lang.*;
import java.lang.reflect.*;
import java.util.*;
import java.io.*;
import zeta.format.*;

/**
  * The FormatPrinter class defines functions for computing and printing
  * Formats for all kinds of Java objects. This can be used to dump Java
  * objects in a readable manner.
  *
  * @author Jacob Wieland (ughosage@cs.tu-berlin.de)
  * @see Format
  */
public class FormatPrinter extends Object {

  /** print format of an Object */
  public static void printFormat(PrintWriter stream, int width, Object ob){
    buildFormat(ob).printFormat(stream,width);
  }

  /** print Format of an integer */
  public static void printFormat(PrintWriter stream, int width, int number){
    buildFormat(number).printFormat(stream,width);
  }

  /** print Format of a short integer */
  public static void printFormat(PrintWriter stream, int width, short number){
    buildFormat((int)number).printFormat(stream,width);
  }

  /** print Format of a long integer */
  public static void printFormat(PrintWriter stream, int width, long number){
    buildFormat((int)number).printFormat(stream,width);
  }

  /** print Format of a byte */
  public static void printFormat(PrintWriter stream, int width, byte bits){
    buildFormat((int)bits).printFormat(stream,width);
  }

  /** print Format of a boolean */
  public static void printFormat(PrintWriter stream, int width, boolean truth){
    buildFormat(truth).printFormat(stream,width);
  }

  /** print Format of a double */
  public static void printFormat(PrintWriter stream, int width, double number){
    buildFormat(number).printFormat(stream,width);
  }

  /** print Format of a float */
  public static void printFormat(PrintWriter stream, int width, float number){
    buildFormat(number).printFormat(stream,width);
  }

  /** This function computes the type of a class as a string and returns
      the last portion of it (everything after the last '.' */
	public static String buildTypeString(Class type) {
		StringBuffer postfix = new StringBuffer();
		while (type.isArray()) {
			postfix = (java.lang.StringBuffer) postfix.append("[]");
			type = type.getComponentType();
		}
		String result = type.getName();
		int pos = result.lastIndexOf('.');
		if (pos >= 0)
			result = result.substring(pos+1);
		return result + postfix;
	}

	private static String capitalize(String s) {
		if (s.length() == 0)
			return s;
	  String result = 
			new String(new char[] {
				Character.toUpperCase(s.charAt(0))
			});
		if (s.length() > 1)
			return result + s.substring(1);
		else
			return result;
	}

  /** build the Format of an object */
  public static Format buildFormat(Object anObject) {
    return buildFormat(new FormatInfo(),anObject);
  }

  /** build the Format of an object (using additional formatting information) */
  public static Format buildFormat(FormatInfo info, Object ob){

    if (ob == null){
		  return new FormatText("null");
		} else if (ob instanceof zeta.format.Formattable) {
      return ((zeta.format.Formattable)ob).toFormat(info);
		} else if (ob instanceof Format) {
			return (Format)ob;
    } else { // custom format
      Class cl = ob.getClass();

      if (cl.isPrimitive()) {
				return buildPrimitiveFormat(info,ob);
			} else if (cl.isArray()) {
				info.addGeneralType(ob,cl);
				return buildArrayFormat(info,ob);
      } else if (ob instanceof Integer || ob instanceof Byte ||
								 ob instanceof Long || ob instanceof Short) {
				return buildFormat(((Integer)ob).intValue());
			} else if (ob instanceof Double) {
				return buildFormat(((Double)ob).doubleValue());
			} else if (ob instanceof Float) {
				return buildFormat(((Float)ob).floatValue());
			} else if (ob instanceof Boolean) {
				return buildFormat(((Boolean)ob).booleanValue());
			} else if (ob instanceof Character) {
				return buildFormat(((Character)ob).charValue());
			} else if (ob instanceof String) {
				return buildStringFormat((String)ob);
			} else { // neither primitive nor array
				info.addGeneralType(ob,cl);
				return buildObjectFormat(info,ob);
			}
		}
	}

  /** build the Format of an int */
	public static Format buildFormat(int number) {
		return new FormatText(Integer.toString(number));
	}

  /** build the Format of a double */
	public static Format buildFormat(double number) {
		return new FormatText(Double.toString(number));
	}

  /** build the Format of a float */
	public static Format buildFormat(float number) {
		return new FormatText(Float.toString(number)+"F");
	}

  /** build the Format of a boolean */
	public static Format buildFormat(boolean truth) {
		return new FormatText(""+truth);
	}

  /** build the Format of a character */
	public static Format buildFormat(char character) {
		return new FormatText("'"+character+"'");
	}

  /** build the Format of a primitive object */
	public static Format buildPrimitiveFormat(FormatInfo info, Object ob) {
		Class cl = ob.getClass();
		Class type = info.generalType(ob);

		if (cl == type)
			return new FormatText(ob.toString());
		else
			return
				new FormatBlock(new Format[] {
					new FormatText(cl.getName()),
					new FormatSpace(),
					new FormatText(ob.toString())
				});
	}

  /** build the Format of a string */
  public static Format buildStringFormat(String s) {
		String[] lines = breakString(s,"\n\r");

		int l = lines.length;
		Vector blocks = new Vector(l/2);

		for (int i = 0; i < l; i++) {
			if (i + 1 < l) {
				if (lines[i].equals("\n")) {
					if (i > 0 && !lines[i-1].equals("\n"))
						blocks.addElement(new FormatLine(new Format[] {
																new FormatText("\""+lines[i-1]+"\\n\""),
																new FormatSpace(),
																new FormatText("+")
															}));
					else
						blocks.addElement(new FormatLine(new Format[] {
																new FormatText("\"\\n\""),
																new FormatSpace(),
																new FormatText("+")
															}));
					blocks.addElement(new FormatSpace());
				}
			} else { // last line
				if (lines[i].equals("\n")) {
					if (i > 0 && !lines[i-1].equals("\n"))
						blocks.addElement(new FormatText("\""+lines[i-1]+"\\n\""));
					else
						blocks.addElement(new FormatText("\"\\n\""));
				} else {
					blocks.addElement(new FormatText("\""+lines[i]+"\""));
				}
			}
		}

		Format[] block = new Format[blocks.size()];
		blocks.copyInto(block);

		return new FormatBeneath(block);
	}

  /** build the Format of an object */
  public static Format buildObjectFormat(FormatInfo info, Object ob){

		Class cl = ob.getClass();
		Class generalType = info.generalType(ob);

		int ref;

		if (info.visited(ob)) {
			return new FormatText("<"+info.visitNumber(ob)+">");
		} else { // never visited before
			ref = info.visit(ob);
		}

		Field[] fields = cl.getFields();
		Object field;
		Format body;

		if (fields.length > 0) {
		  Vector memberNames = new Vector();
		  Vector memberVals = new Vector();

			Class type;

			for (int i = 0; i < fields.length; i++){
				// only show non-static, public fields which do not 
				// contain $'s in their name
				// (whether private and $-fields are shown should be 
				//  perhaps configurable by a global flag)
			  int mods = fields[i].getModifiers();
				if (!Modifier.isStatic(mods)
						 && fields[i].getName().indexOf("$") < 0){
				  Format fieldFormat;
				  type = fields[i].getType();
					try{
						field = fields[i].get(ob);
						info.addGeneralType(field,type);
						fieldFormat = buildFormat(info, field);
					}
					catch (IllegalAccessException e){
						fieldFormat = new FormatText("<not accessible>");
					}
				  memberNames.addElement(
					             new FormatLine(new Format[] {
				  								new FormatText(buildTypeString(type)),
				  								new FormatSpace(),
				  								new FormatText(1,fields[i].getName())
				  							})
								);
				  memberVals.addElement(fieldFormat);
				}
			}
			body =
				new FormatLine(new Format[] {
					new FormatLine(new Format[] {
						new FormatText(buildTypeString(cl)),
						new FormatSpace(),
						new FormatText("{")
					}),
					new FormatSpace(),
				  ((NestedFormat)buildMembersFormat(info,memberNames,memberVals))
					                                              .nested(1),
					new FormatSpace(),
					new FormatText("}")
				});
		} else {
			body =
				new FormatLine(new Format[] {
					new FormatText(buildTypeString(cl)),
					new FormatSpace(),
					new FormatLine(new Format[] {
						new FormatText("{"),
						new FormatText("}")
					})
				});
		}

		return
			new FormatLine(new Format[] {
				new FormatText("<"+ref+">"),
				new FormatSpace(),
				body
			});
	}

  /** build the Format of an array */
	public static Format buildArrayFormat(FormatInfo info, Object array){

	  Class cl = info.generalType(array);
		int ref;

		if (info.visited(array)) {
			return new FormatText("<"+info.visitNumber(array)+">");
		} else { // never visited before
			ref = info.visit(array);
		}

		Format[] block;

		int l = Array.getLength(array);
		Class componentType = cl.getComponentType();

		if (l > 0)
			block = new Format[2*l-1];
		else
			block = new Format[0];

		Format componentFormat;
		String componentTypeName = componentType.getName();

		int arrayTypeSwitch = 0;
		if (componentTypeName.equals("int") ||
				componentTypeName.equals("short") ||
				componentTypeName.equals("long") ||
				componentTypeName.equals("byte")) {
			arrayTypeSwitch = 1;
		} else if (componentTypeName.equals("double")) {
			arrayTypeSwitch = 2;
		} else if (componentTypeName.equals("float")) {
			arrayTypeSwitch = 3;
		} else if (componentTypeName.equals("boolean")) {
			arrayTypeSwitch = 4;
		} else if (componentTypeName.equals("char")) {
			arrayTypeSwitch = 5;
		}

		Object component;

		for (int i = 0; i < l; i++) {
			switch (arrayTypeSwitch) {
			case 1:
				componentFormat = buildFormat(Array.getInt(array,i));
				break;
			case 2:
				componentFormat = buildFormat(Array.getDouble(array,i));
				break;
			case 3:
				componentFormat = buildFormat(Array.getFloat(array,i));
				break;
			case 4:
				componentFormat = buildFormat(Array.getBoolean(array,i));
				break;
			case 5:
				componentFormat = buildFormat(Array.getChar(array,i));
				break;
			default:
				component = Array.get(array,i);
				info.addGeneralType(component,componentType);
				componentFormat = buildFormat(info,component);
				break;
			}

			if (i < l - 1) {
				block[2*i] =
					new FormatAppend(new Format[] {
						componentFormat,
						new FormatText(",")
					});
				block[2*i+1] = new FormatSpace();
			} else { // last element
				block[2*i] = componentFormat;
			}
		}

		Format body;

		if (block.length == 0) {
			body =
				new FormatLine(new Format[] {
					new FormatText(buildTypeString(cl)),
					new FormatSpace(),
					new FormatLine(new Format[] {
						new FormatText("{"),
						new FormatText("}")
					})
				});
		} else {
			body =
				new FormatLine(new Format[] {
					new FormatLine(new Format[] {
						new FormatText(buildTypeString(cl)),
						new FormatSpace(),
						new FormatText("{")
					}),
					new FormatSpace(),
					new FormatBlock(1,block),
					new FormatSpace(),
					new FormatText("}")
				});
		}

		return
			new FormatLine(new Format[] {
				new FormatText("<"+ref+">"),
				new FormatSpace(),
				body
			});
	}

	// only for compatibility reasons
  /** build the Format of a hashtable */
	public static Format buildHashtableFormat(FormatInfo info, Hashtable table){

		if (table.isEmpty())
			return new FormatBlock(new Format[0]);

		Format[] block = new Format[2*table.size()-1];

		Enumeration keys = table.keys();
		Object key;
		Object field;

		for (int i = 0; keys.hasMoreElements(); i++) {
			key = keys.nextElement();
			field = table.get(key);
			info.addGeneralType(field,field.getClass());
			info.addGeneralType(key,key.getClass());
			block[2*i] =
				new FormatBlock(new Format[] {
					new FormatAppend(new Format[] {
						buildFormat(info,key),
						new FormatText(":")
					}),
					new FormatSpace(),
					new FormatAppend(1,new Format[] {
						buildFormat(info,field),
						new FormatText(";")
					}),
					new FormatBreak()
				});
			if (keys.hasMoreElements()) 
				block[2*i+1] = new FormatSpace();
		}

		return new FormatBlock(block);
	}

  /** build Format for list of members of a class (used by buildObjectFormat) */
	public static Format buildMembersFormat(FormatInfo info, 
													                Vector names,
																					Vector vals){

		if (names.isEmpty())
			return new FormatBlock(new Format[0]);

		Format[] block = new Format[2*names.size()-1];

		Object key;
		Object field;

		for (int i = 0; i < names.size(); i++){
				key = names.elementAt(i);
				field = vals.elementAt(i);
				info.addGeneralType(field,field.getClass());
				info.addGeneralType(key,key.getClass());
				block[2*i] =
					new FormatBlock(new Format[] {
						new FormatAppend(new Format[] {
								buildFormat(info,key),
								new FormatText(":")
						}),
						new FormatSpace(),
						new FormatAppend(1,new Format[] {
								buildFormat(info,field),
								new FormatText(";")
						}),
						new FormatBreak()
				  });
			  if (i + 1 < names.size())
				  block[2*i+1] = new FormatSpace();
		}

		return new FormatBlock(block);
	}

	/** build the Format for a string with newlines */
	public static Format buildTextFormat(String text){
		StringTokenizer tkns = new StringTokenizer(text, "\n\r");
		Vector buf = new Vector();
		while (tkns.hasMoreTokens()){
			buf.addElement(new FormatText(tkns.nextToken()));
		}
		Format[] formats = new Format[buf.size()];
		buf.copyInto(formats);
		return new FormatBeneath(formats);
	}

	/**
   * This function breaks the given text at the given delimiters.
   *
   * @param text the string to be broken
   * @param delimiters a string containing delimiter characters
   *
   * @return an array of strings and delimiters
   */
  public static String[] breakString(String text, String delimiters) {
    int l = text.length();
    Vector words = new Vector(l/4);
    int lastDelimiterIndex = -1;

    for (int i = 0; i < l; i++) {
      if (delimiters.indexOf(text.charAt(i)) >= 0) { // character a delimiter?
				if (lastDelimiterIndex < i-1) // only add if it is not the empty string
					words.addElement(text.substring(lastDelimiterIndex+1,i));
				words.addElement(text.substring(i,i+1));
				lastDelimiterIndex = i;
      }
    }
    if (lastDelimiterIndex < l - 1) {
      words.addElement(text.substring(lastDelimiterIndex+1,l));
    }

    String[] result = new String[words.size()];
    words.copyInto(result);
    return result;
  }
			
}
