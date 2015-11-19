package zeta.format.impl;

import java.lang.String;
import java.io.PrintWriter;
import zeta.format.*;


/**
  * This class is a basic Format containing a String without
  * newlines. All spaces within the text will never be ignored.
  * </p>
  * A further implementation could allow newlines, as well, but would
  * have to implement a different width/height behaviour as well as
  * a different print-behaviour, of course.
  * </p>
  * The text may also have an own indentation.
  *
  * @author Jacob Wieland (ughosage@cs.tu-berlin.de)
  *
  * @see Format
  * @see NestedFormat
  * @see FormatStream
  */
public class FormatText extends NestedFormat {
  public String text; // a text without any newlines

  public int minHeight()    { return 1; }
  public int minWidth()     { return text.length(); }
  public int maxWidth()     { return text.length(); }
  public int minLastWidth() { return text.length(); }
  public int maxLastWidth() { return text.length(); }

  public FormatText(int indentation, String text) {
    super(indentation);
    this.text = text;
  }

  public FormatText(String text) {
    this(0,text);
  }

  public int appendText(int indentation, FormatStream stream) {
    stream.printText(indentation,text);
    return text.length();
  }

  public TextRectangle printTextBeside(int indentation, FormatStream stream,
                                       int width, int lastWidth) {
    return new TextRectangle(appendText(indentation, stream));
  }

  /** */
  public void dumpText(PrintWriter writer){
    writer.write(text);
  }

}
