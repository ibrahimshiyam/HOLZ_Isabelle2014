package zeta.format.impl;

/**
  * This compound Format class is for Formats that should be appended to
  * one another. If the text of one component Format does not fit on the
  * rest of the line (into the given width), a new line is opened before
  * printing that text.
  * </p>
  * This is for instance very useful for the printing of the contents of an
  * array. As long as the next item still fits into the current line, it gets
  * printed, if the next item would not fit, then a new line is opened first,
  * where the item then will be printed instead.
  * </p>
  * The text-rectangle of a FormatBlock format could look like this:
  <pre>
  ....______________.....
  :..|_____|________|   :
  : |          |        :
  : |    ______|________:
  :.|___|_____|_____|___|
  :   |           |     :
  :   |     ______|.....:
  :...|____|

  </pre>
  * @author Jacob Wieland (ughosage@cs.tu-berlin.de)
  * 
  * @see CompoundFormat
  * @see Format
  */
import zeta.format.*;
public class FormatBlock extends CompoundFormat {

  public FormatBlock(int indentation, Format[] formats) {
    super(indentation,formats);
  }

  public FormatBlock(Format[] formats) {
    super(formats);
  }

	public FormatBlock(int indentation, String text, String delimiters) {
		super(indentation,text,delimiters);
	}

	public FormatBlock(String text, String delimiters) {
		this(0,text,delimiters);
	}

	public FormatBlock(String text) {
		super(text);
	}

  /* Convenience constructors: */
  public FormatBlock(int indent, Format f1, Format f2) {
    this(indent, new Format[] { f1, f2 });
  }
  public FormatBlock(int indent, Format f1, Format f2, Format f3) {
    this(indent, new Format[] { f1, f2, f3 });
  }
  public FormatBlock(int indent, Format f1, Format f2, Format f3, Format f4) {
    this(indent, new Format[] { f1, f2, f3, f4 });
  }
  public FormatBlock(Format f1, Format f2) {
    this(new Format[] { f1, f2 });
  }
  public FormatBlock(Format f1, Format f2, Format f3) {
    this(new Format[] { f1, f2, f3 });
  }
  public FormatBlock(Format f1, Format f2, Format f3, Format f4) {
    this(new Format[] { f1, f2, f3, f4 });
  }
  public FormatBlock(int indent, Format f1, Format f2, Format f3, 
		      Format f4, Format f5) 
  {
    this(indent, new Format[] { f1, f2, f3, f4, f5 });
  }
  public FormatBlock(Format f1, Format f2, Format f3, Format f4, Format f5) {
    this(new Format[] { f1, f2, f3, f4, f5 });
  }
  public FormatBlock(int indent, Format f1, Format f2, Format f3, 
		      Format f4, Format f5, Format f6) {
    this(indent, new Format[] { f1, f2, f3, f4, f5, f6 });
  }
  public FormatBlock(Format f1, Format f2, Format f3, Format f4, Format f5,
                      Format f6) 
  {
    this(new Format[] { f1, f2, f3, f4, f5, f6 });
  }

  protected int computeMaxWidth() {
    int usedWidth = 0, maxUsedWidth = 0;
    int l = formats.length;

    for (int i = 0; i < l; i++) {

      if (formats[i].minHeight() > 1) {
        if ((usedWidth = formats[i].maxWidth()) > maxUsedWidth)
          maxUsedWidth = usedWidth;
        // broken blocks always stand at the beginning of the line
        usedWidth = formats[i].maxLastWidth();
      } else {
        usedWidth += formats[i].maxWidth();
        if (usedWidth > maxUsedWidth)
          maxUsedWidth = usedWidth;
      }
    }

    return maxUsedWidth;
  }

  protected int computeMaxLastWidth() {
    int usedWidth = 0;

    for (int i = formats.length; i-->0; ) {

      usedWidth += formats[i].maxLastWidth();

      if (formats[i].minHeight() > 1) 
        break;
    }

    return usedWidth;
  }

  protected int computeMinHeight() {
    int usedHeight = 1;

    for (int i = formats.length; i-->0; )
      usedHeight += formats[i].minHeight() - 1;

    return usedHeight;
  }

  public TextRectangle printTextBeside(int indentation, FormatStream stream,
                                       int width, int lastWidth) {
    int l = formats.length;

    int usedHeight = 1;
    int usedWidth = 0;
    int maxUsedWidth = 0;

    int maxWidth;
    int w;
    TextRectangle r;

    for (int i = 0; i < l; i++) {

      // ignore spaces at the beginning of lines
      // the first format is not at the beginning of a line
      if (stream.atLineBegin() && formats[i] instanceof FormatSpace)
        continue;

      if (i < l-1)
        w = width;
      else
        w = lastWidth;

      if (formats[i].minHeight() > 1 || 
          usedWidth + (maxWidth = formats[i].maxLastWidth()) > w) {

        // break, if it is not a break and we're not at the beginning of line
        if (i > 0 &&
            !(stream.atLineBegin() || formats[i] instanceof FormatBreak)) {
          stream.printBreaks(1);
          usedHeight++;
        }
        
        if (formats[i] instanceof FormatSpace)
          continue;

        // print the text with its own indentation added
        r = formats[i].printText(indentation,stream,width,w);

        // set the used-up width for the next text to this block's last width
        usedWidth = r.lastWidth;

        // if the text was wider than any other up till now, 
        // remember this widest width in maxUsedWidth
        if (r.width > maxUsedWidth)
          maxUsedWidth = r.width;

        // increase the used height by one less than the height of the block
        usedHeight += r.height - 1;

      } else { // it could fit on the rest of the last line

        // print the text beside the other texts on this line
        r = formats[i].printTextBeside(indentation+usedWidth,
                                       stream,maxWidth);

        // increase the usedWidth of the current line and the maxUsedWidth
        // if the current line is then the widest line up till now
        usedWidth += r.lastWidth;

        if (usedWidth > maxUsedWidth)
          maxUsedWidth = usedWidth;

        // Do _not_ increase the usedHeight since it would be
        // increased by r.height - 1 (which is 0)
      }
    } 
    return new TextRectangle(maxUsedWidth,usedHeight,usedWidth);
  }
}
