package zeta.format.impl;

import java.io.PrintWriter;
import zeta.format.*;

/**
  * This is the basic Format class for forced newlines.
  * It can contain a number of newlines.
  * </p>
  * Upon printing, the contained number of newlines is given to the
  * FormatStream and printed. Afterwards, the stream is at the beginning
  * of a new line.
  *
  * @author Jacob Wieland (ughosage@cs.tu-berlin.de)
  *
  * @see Format
  * @see FormatStream
  */
public class FormatBreak extends Format {
  int lines;

  public int minHeight()    { return lines+1; }
  public int minWidth()     { return 0; }
  public int maxWidth()     { return 0; }
  public int minLastWidth() { return 0; }
  public int maxLastWidth() { return 0; }

  public FormatBreak(int lines) {
    // all widths of a break are 0
    super();
    this.lines = lines;
  }

  public FormatBreak() {
    this(1);
  }

  // This makes no sense and should never be called unless lines == 0 
  public int appendText(int indentation, FormatStream stream) {

    // do nothing

    return 0;
  }

  /** */
  public TextRectangle printTextBeside(int indentation, FormatStream stream,
                                       int width, int lastWidth) {

    stream.printBreaks(lines);

    return new TextRectangle(0,lines+1,0);
  }

  /** */
  public void dumpText(PrintWriter writer){
    writer.println();
  }

}
