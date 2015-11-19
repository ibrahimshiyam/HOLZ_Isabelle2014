package zeta.format.impl;

/**
  * This is the Format class for spaces that can be ignored at the beginning
  * and end of a line.
  * The space can have a width that is more than 1.
  *
  * @author Jacob Wieland (ughosage@cs.tu-berlin.de)
  *
  * @see Format
  * @see FormatStream
  */

import java.io.PrintWriter;
import zeta.format.*;

public class FormatSpace extends Format {
  private int width;

  public int minHeight()    { return 1; }
  public int minWidth()     { return width; }
  public int minLastWidth() { return width; }
  public int maxWidth()     { return width; }
  public int maxLastWidth() { return width; }

  public FormatSpace(int width) {
    super();
    this.width = width;
  }

  public FormatSpace() {
    this(1);
  }

  public int appendText(int indentation, FormatStream stream) {
    stream.printSpaces(width);
    return width;
  }

  public TextRectangle printTextBeside(int indentation, FormatStream stream,
                                       int width, int lastWidth) {
    return new TextRectangle(appendText(indentation,stream));
  }

  /** */
  public void dumpText(PrintWriter writer){
    writer.write(" ");
  }
}
