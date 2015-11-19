package zeta.format.impl;

/**
  * This is a compound Format class for component Format texts that should
  * either be printed into one line (if they all would fit into that line) or
  * beneath each other.
  * </p>
  * This behaviour is especially useful for lists of items that are quite
  * complex, so it would not be wise to print several of them into one
  * line for more than one line, since that could lead to confusion for
  * the reader.
  *
  * @author Jacob Wieland (ughosage@cs.tu-berlin.de)
  *
  * @see CompoundFormat
  * @see Format
  */
import zeta.format.*;
public class FormatLine extends CompoundFormat {

  public FormatLine(int indentation, Format[] formats) {
    super(indentation,formats);
  }

  public FormatLine(Format[] formats) {
    super(formats);
  }

  protected int computeMaxWidth() {
    int usedWidth;
    int maxUsedWidth = 0;
    int l = formats.length;

    for (int i = 0; i < l; i++) {
      if (formats[i].minHeight() > 1) {
        maxUsedWidth = 0;
        for (i = 0; i < l; i++)
          if ((usedWidth = formats[i].maxWidth()) > maxUsedWidth)
            maxUsedWidth = usedWidth;
        break;
      }
      maxUsedWidth += formats[i].maxWidth();
    }

    return maxUsedWidth;
  }

  protected int computeMaxLastWidth() {
    int usedWidth = 0;

    // look up the last block that has more than one line
    // if one is found, take the lastWidth of that block plus the 
    // maxWidhts of all following blocks as maxLastWidth

    for (int i = formats.length; i-->0; ) {
      usedWidth += formats[i].maxLastWidth();
      if (formats[i].minHeight() > 1) 
        break;
    }

    return usedWidth;
  }

  protected int computeMinHeight() {
    int usedHeight = 0;
    int height;
    boolean broken = false;

    // if all blocks contain no newline, the height is 1,
    // otherwise its the sum of the minimal heights of all the blocks
    for (int i = formats.length; i-->0; ) {
			if (formats[i] instanceof FormatSpace)
				continue;
      usedHeight += height = formats[i].minHeight();

      if (height > 1)
        broken = true;
    }

    return broken ? usedHeight : 1;
  }

  public TextRectangle printTextBeside(int indentation, FormatStream stream,
                                       int width, int lastWidth) {
    int i;
    int l = formats.length;
    int usedWidth = 0;
    int[] maxWidths = new int[l];

    // Print the texts only beside each other, if _all_ of them fit 
    // into one line of the given width
    for (i = 0; usedWidth <= lastWidth && i < l; i++) {
      if (formats[i].minHeight() > 1)
        break;
      usedWidth += maxWidths[i] = formats[i].maxLastWidth();
    }
    
    // If not all of the blocks fit into one line of the given width
    // use the default printing behaviour (beneath each other)
    if (i < l || usedWidth > lastWidth)
      return super.printTextBeside(indentation,stream,width,lastWidth);

    usedWidth = 0;

    for (i = 0; i < l; i++) {
      // just print the text
      formats[i].appendText(indentation+usedWidth,stream);
      usedWidth += maxWidths[i];
    }

    return new TextRectangle(usedWidth);
  }
}
