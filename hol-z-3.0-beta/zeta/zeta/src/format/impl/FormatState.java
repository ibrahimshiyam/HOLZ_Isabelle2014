package zeta.format.impl;

/**
  * A class which realizes a state-oriented frontend to
  * the formatting facilities. 
  *
  * @version $Id: FormatState.java,v 1.1.1.1 1998/09/01 10:51:16 wg Exp $
  * @author Wolfgang Grieskamp
  */

import java.util.Stack;
import java.util.Vector;
import java.io.PrintWriter;

import java.io.FileWriter;
import java.io.FileDescriptor;

import zeta.format.*;


public class FormatState {

  /** The current vector to append formats to. */
  private Vector formats = new Vector();

  /** The indentation used on line breaks. */
  private int indent = 0;

  /** A stack of outer formats. */
  private Stack formatsStack = new Stack();

  /** A stack for indentation of outer formats. */
  private Stack indentStack = new Stack();

  /** Construct a new format state. */
  public FormatState(){}

  /** Append a format to format state. */
  public void add(Format fmt){
    formats.addElement(fmt);
  }

  /** Append a literal to the format state. */
  public void lit(String lit){
    formats.addElement(new FormatText(lit));
  }

  /** Append a line break to the format state. */
  public void brk(){
    formats.addElement(new FormatBreak());
  }

  /** Append a space to the format state. */
  public void spc(){
    formats.addElement(new FormatSpace());
  }

  /** Append a space to the format state. */
  public void spc(int count){
    formats.addElement(new FormatSpace(count));
  }

  /** Begin a new nested block. */
  public void beg(int indent){
    formatsStack.push(formats);
    indentStack.push(new Integer(this.indent));
    formats = new Vector();
    this.indent = indent;
  }

  /** End a nested block. */
  public void end(){
    Format block = toFormat();
    formats = (Vector) formatsStack.pop();
    formats.addElement(block);
    indent = ((Integer)indentStack.pop()).intValue();
  }

  /** Return format in state. */
  public Format toFormat(){
    Format[] array = new Format[formats.size()];
    formats.copyInto(array);
    return new FormatBlock(indent, array);
  }

  /** Output format in state to a PrintWriter. */
  public void print(PrintWriter writer, int width){
    toFormat().printFormat(writer,width);
  }

}

/*
public class Test {

  public static void main(String[] argv){
    FormatState s = new FormatState();
    PrintWriter w = new PrintWriter(new FileWriter(FileDescriptor.out));
    w.println("start");
    s.lit("Hello World!");
    s.beg(2);
    for (int i = 0; i < 32; i++) { s.lit("<HELLO>"); s.spc(2); }
    s.end();
    s.lit("bye");
    s.print(w, 70);
    w.close();
  }
}
*/
