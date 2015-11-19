package zeta.format.impl;

import java.lang.String;
import java.io.PrintWriter;
import zeta.format.*;


/**
  * This class is a basic Format containing nothing and doing nothing
  * upon printing. 
  *
  * @author Jacob Wieland (ughosage@cs.tu-berlin.de)
  *
  * @see Format
  * @see FormatStream
  */
public class FormatEmpty extends Format {
  public int minHeight()    { return 0; }
  public int minWidth()     { return 0; }
  public int maxWidth()     { return 0; }
  public int minLastWidth() { return 0; }
  public int maxLastWidth() { return 0; }

  public int appendText(int indentation, FormatStream stream) {
    // do nothing
    return 0;
  }

  public TextRectangle printTextBeside(int indentation, FormatStream stream,
                                       int width, int lastWidth) {
    // do nothing
    return new TextRectangle(0,0,0); // no height, no width
  }

  /** */
  public void dumpText(PrintWriter writer){
  }
}
