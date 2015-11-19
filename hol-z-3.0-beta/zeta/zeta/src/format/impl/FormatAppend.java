package zeta.format.impl;
import zeta.format.*;

/**
  * This is a compound Format class for a list of Formats that should be
  * printed 'beside' each other like it is done for FormatBeside.
  * This means, that each text is printed beside the end of the last line
  * of the text before it.
  * However, unlike for FormatBeside, which prints the Formats beneath each
  * other, if the text would otherwise become too wide, FormatAppend prints
  * its components 'beside' each other in every case,
  * so it should be used very carefully.
  * </p>
  * The append-behaviour is especially useful for interpunctions that should
  * normally not be printed on the beginning of a new line. Instead the
  * break should be made before the block preceding the item to be appended.
  *
  * @author Jacob Wieland (ughosage@cs.tu-berlin.de)
  *
  * @see FormatBeside
  */
public class FormatAppend extends CompoundFormat {

  public FormatAppend(int indentation, Format[] formats) {
    super(indentation,formats);
  }

  public FormatAppend(Format[] formats) {
    super(formats);
  }

  /* Convenience constructors: */
  public FormatAppend(int indent, Format f1) {
    this(indent, new Format[] { f1 });
  }
  public FormatAppend(int indent, Format f1, Format f2) {
    this(indent, new Format[] { f1, f2 });
  }
  public FormatAppend(int indent, Format f1, Format f2, Format f3) {
    this(indent, new Format[] { f1, f2, f3 });
  }
  public FormatAppend(int indent, Format f1, Format f2, Format f3, Format f4) {
    this(indent, new Format[] { f1, f2, f3, f4 });
  }
  public FormatAppend(Format f1, Format f2) {
    this(new Format[] { f1, f2 });
  }
  public FormatAppend(Format f1, Format f2, Format f3) {
    this(new Format[] { f1, f2, f3 });
  }
  public FormatAppend(Format f1, Format f2, Format f3, Format f4) {
    this(new Format[] { f1, f2, f3, f4 });
  }
  public FormatAppend(int indent, Format f1, Format f2, Format f3, 
		      Format f4, Format f5) 
  {
    this(indent, new Format[] { f1, f2, f3, f4, f5 });
  }
  public FormatAppend(Format f1, Format f2, Format f3, Format f4, Format f5) {
    this(new Format[] { f1, f2, f3, f4, f5 });
  }
  public FormatAppend(int indent, Format f1, Format f2, Format f3, 
		      Format f4, Format f5, Format f6) {
    this(indent, new Format[] { f1, f2, f3, f4, f5, f6 });
  }
  public FormatAppend(Format f1, Format f2, Format f3, Format f4, Format f5,
                      Format f6) 
  {
    this(new Format[] { f1, f2, f3, f4, f5, f6 });
  }

  protected int computeMaxWidth() {
    int maxWidth = 0;
    int usedWidth = 0;
    int maxMaxWidth = 0;
    int l = formats.length;

    for (int i = 0; i < l; i++) {
      if (i > 0)
        usedWidth += formats[i-1].maxLastWidth();
      else
        usedWidth = 0;
      if ((maxWidth = usedWidth + formats[i].maxWidth()) > maxMaxWidth)
        maxMaxWidth = maxWidth;
    }
    return maxMaxWidth;
  }

  protected int computeMaxLastWidth() {
    int usedWidth = 0;

    for (int i = formats.length; i-->0; )
      usedWidth += formats[i].maxLastWidth();

    return usedWidth;
  }

  protected int computeMinHeight() {
    int usedHeight = 1;

    for (int i = formats.length; i-->0; )
      usedHeight += formats[i].minHeight() - 1;

    return usedHeight;
  }

	protected int computeMinWidth() {
		int usedWidth = 0;
		int maxUsedWidth = 0;
		int l = formats.length;
		int width;

		for (int i = 0; i < l; i++) {
			if (usedWidth + (width = formats[i].minWidth()) > maxUsedWidth)
				maxUsedWidth = usedWidth + width;
			usedWidth += formats[i].minLastWidth();
		}

		return maxUsedWidth;
	}

	protected int computeMinLastWidth() {
		int usedWidth = 0;
		int l = formats.length;

		for (int i = 0; i < l; i++) {
			usedWidth += formats[i].minLastWidth();
		}

		return usedWidth;
	}

  public TextRectangle printTextBeside(int indentation, FormatStream stream,
                                       int width, int lastWidth) {
    int i;
    int l = formats.length;
    int neededWidth = 0;
    int[] minLastWidths = new int[l];

    // compute the total width minimally needed to print all
    // formats beside each other

    for (i = 0; i < l; i++) {
      // increase the needed width (for blocks 0..i) by the minimal width of
      // the last line
      neededWidth += minLastWidths[i] = formats[i].minLastWidth();
    }

    // Print each block beside the last line of the block before
    //-----------------------------------------------------------

    // usedWidth stores the sum of the lengths of last lines of the
    // already printed blocks
    // Thus, indentation+usedWidth is the indentation for the next block
    int usedWidth = 0;

    // usedHeight stores the sum of lines already printed
    int usedHeight = 1;

    // maxUsedWidth stores the width of the longest line that was printed
    int maxUsedWidth = 0;

    TextRectangle r;

    for (i = 0; i < l; i++) {
      // further needed width <- sum(minWidths[i+1..])
      neededWidth -= minLastWidths[i];

      // print the block beside the used indentation with the maximally
      // usable width and the maximally usable width for the last line
      // for that block
      r = formats[i].printTextBeside(indentation + usedWidth,
                                     stream,
                                     width - usedWidth,
                                     lastWidth - (usedWidth + neededWidth));

      // if the longest line of this block (the longest line 
      // plus its indentation) was longer than the longest line up to now,
      // then store the length of this line as the maximally used width
      if (usedWidth + r.width > maxUsedWidth)
        maxUsedWidth = usedWidth + r.width;

      // increase the indentation for the next block by the length of the last
      // line of the just printed block
      usedWidth += r.lastWidth;

      // increase the used height by one less than the height of the just
      // printed block (the first line was printed in the last line of
      // the last block and thus didn't add any 'height' to the text)
      usedHeight += r.height - 1;
    }
    return new TextRectangle(maxUsedWidth,usedHeight,usedWidth);
  }


}
