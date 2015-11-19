package zeta.format.impl;

import java.util.Vector;
import java.io.PrintWriter;
import zeta.format.*;

/**
  * This abstract class shall be inherited by all Format classes that 
  * are essentially built up out of a list of other Formats.
  * It also implements the default-behaviour of printing such a compound
  * Format.
  * </p>
  * This default behaviour prints each of the component Formats below
  * the previous ones, printing a newline after each of them (except the last).
  * </p>
  * Here an example how text-rectangles are formed by formats beneath each
  * other:
  <pre>
  ...._______________________.....
  :  |                       |   :
  :  |                       |   :
  :  |             __________|   :
  :..|____________|______________:
  :    |                         |
  :    |   ______________________|
  :....|__|______................:
  :...|__________|
  </pre>
  *
  * @author Jacob Wieland (ughosage@cs.tu-berlin.de)
  * 
  * @see NestedFormat
  * @see Format
  * @see FormatBlock
  * @see FormatBeside
  * @see FormatBeneath
  * @see FormatLine
  */

public abstract class CompoundFormat extends NestedFormat {
  /**
    * An array of component formats.
    * 
    * @see Format
    */

  private static final String newl = System.getProperty("line.separator");

  // protected
  public Format[] formats;

  // protected
  public int maxWidth, minWidth, maxLastWidth, minLastWidth, minHeight;

  public int maxWidth()     { return maxWidth;     }
  public int minWidth()     { return minWidth;     }
  public int minHeight()    { return minHeight;    }
  public int maxLastWidth() { return maxLastWidth; }
  public int minLastWidth() { return minLastWidth; }

	private void initFormats(Format[] formats) {
    this.formats = formats;
    this.minWidth = computeMinWidth();
    this.maxWidth = computeMaxWidth();
    this.minLastWidth = computeMinLastWidth();
    this.maxLastWidth = computeMaxLastWidth();
    this.minHeight = computeMinHeight();
	}

  /**
    * This constructor sets the indentation, the component formats and
    * also computes the values for the minimal/maximal widths and height.
    *
    * @param indentation the own indentation of this CompoundFormat
    * @param formats the component formats of this CompoundFormat
    *
    * @see NestedFormat
    * @see Format
    */
  public CompoundFormat(int indentation, Format[] formats) {
    super(indentation);
		initFormats(formats);
  }

  /**
    * This is a shortcut-constructor for CompoundFormats without own
    * indentation.
    */
  public CompoundFormat(Format[] formats) {
    this(0,formats);
  }

	/**
		* @param indentation the indenation of this compound format
		* @param text a string that will be broken at the given delimiters
		* The broken string is computed into an array of text, space and break
		* Formats.
		* @param delimiters the delimiter characters by which the text should
		*	be broken
		* 
		*/
	public CompoundFormat(int indentation, String text, String delimiters) {
		super(indentation);
		String[] words = FormatPrinter.breakString(text,delimiters);
		Format[] formats = new Format[words.length];
		for (int i = words.length; i-->0; ) {
			if (words[i].equals(" "))
				formats[i] = new FormatSpace();
			else if (words[i].equals(newl))
				formats[i] = new FormatBreak();
		  else
				formats[i] = new FormatText(words[i]);
		}
		initFormats(formats);
	}

	public CompoundFormat(int indentation, String text) {
		this(indentation, text," \n\r"); // default delimiters: space and newline
	}

	public CompoundFormat(String text) {
		this(0,text);
	}

  protected abstract int computeMaxWidth();
  protected abstract int computeMaxLastWidth();
  protected abstract int computeMinHeight();

  protected int computeMinWidth() { 
    int maxMinWidth = 0;
    int minWidth;

    for (int i = formats.length; i-->0; ) {
      if ((minWidth = formats[i].minWidth() + formats[i].nesting()) >
					maxMinWidth)
        maxMinWidth = minWidth;
    }
    return maxMinWidth;
  }

  protected int computeMinLastWidth() {
    int l = formats.length;

    if (l > 0)
      return formats[l-1].minLastWidth() + formats[l-1].nesting();
    return 0;
  }

  public int appendText(int indentation, FormatStream stream) {
    int usedWidth = 0;

    // append all Formats to the line
    for (int i = 0; i < formats.length; i++)
      usedWidth += formats[i].appendText(indentation+usedWidth,stream);

    return usedWidth;
  }

  public TextRectangle printTextBeside(int indentation, FormatStream stream,
                                       int width, int lastWidth) {
    int l = formats.length;

    int maxUsedWidth = 0;
    int usedWidth = 0;
    int usedHeight = 0;

    int w;

    TextRectangle r;

    for (int i = 0; i < l; i++) {

      // ingore all spaces 
      if (formats[i] instanceof FormatSpace)
        continue;

      if (i < l-1)
        w = width;
      else
        w = lastWidth;

      // print the block with its own indentation added
      r = formats[i].printText(indentation,stream,width,w);

      usedWidth = r.width;

      if (usedWidth > maxUsedWidth)
        maxUsedWidth = usedWidth;

      usedHeight += r.height;

      // print a break after all blocks before the last that didn't end
      // in a break anyway
      if (i < l-1) {
        if (!stream.atLineBegin()) {
          stream.printBreaks(1);
          usedHeight++;
        }
      } else {
        usedWidth = r.lastWidth;
      }
    }

    return new TextRectangle(maxUsedWidth,usedHeight,usedWidth);
  }

  public void dumpText(PrintWriter writer){
    for (int i = 0; i < formats.length; i++){
      formats[i].dumpText(writer);
    }
  }

}
