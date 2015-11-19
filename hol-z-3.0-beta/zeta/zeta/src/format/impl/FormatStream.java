package zeta.format.impl;

import java.lang.Object;
import java.lang.String;
import java.io.PrintWriter;
import java.util.Vector;
import zeta.format.*;

/**
  * This class contains a PrintWriter and prints texts, spaces and 
  * newlines on that stream. It ignores Spaces at the beginnings and
  * ends of lines. It also provides a means to test, wether the stream
  * is currently at the begin of a line.
  * </p>
  * It is used by the basic Format classes FormatText, FormatBreak and
  * FormatSpace, as well as the compound Format classes FormatBlock,
  * FormatBeside, FormatAppend, FormatLine and FormatBeneath.
  *
  * @author Jacob Wieland (ughosage@cs.tu-berlin.de)
  *
  * @see Format
  * @see FormatText
  * @see FormatBreak
  * @see FormatSpace
  * @see FormatBlock
  * @see FormatBeside
	* @see FormatAppend
  * @see FormatBeneath
  * @see FormatLine
  */
public class FormatStream extends Object {
  private PrintWriter output;
	private StringBuffer line;
  private int spaceWidth;
	private boolean wrapAround;
	private int width;

  // constructors

	/**
		* @param output the stream on which the format string shall be printed
		* @param wrapAround a flag that enables wrap-around behaviour for lines
		* that are longer than the given width
		* @param width the width that should not be exceeded, if wrapping around
		* should take place
		*/
	public FormatStream(PrintWriter output, boolean wrapAround, int width) {
    super();
		this.width = width;
		this.output = output;
		this.wrapAround = wrapAround;
		line = new StringBuffer(width);
	}

	public FormatStream(PrintWriter output, int width) {
		this(output,false,width);
	}

  public FormatStream(PrintWriter output) {
		this(output,79);
  }

  /**
    * @return true if the stream is at the begin of a line
    */
  public boolean atLineBegin() {
		return line.length() == 0;
  }

  /**
    * This method stores the number of given spaces to be printed,
    * if some text is to be printed afterwards
    *
    * @param width the number of spaces to be printed
    */
  public void printSpaces(int width) {

    // ignore spaces at the beginning of a line
    if (atLineBegin())
      return;

    // increase the number of spaces to be printed before the next
    // text in the same line
    spaceWidth += width;
  }

  /**
    * This method first prints the accumulated characters in the current line,
		* wrapping around if necessary (if the line is longer than the width of
		* the stream) and prints the given number of newlines afterwards.
		*
    * This method is used by the FormatBreak class as well as the
    * CompoundFormat and FormatBlock classes.
		* It is also used by the printEndOfFormat method in this class.
    *
    * @param lines The number of newlines to be printed
    *
    * @see FormatBreak#printTextBeside
    * @see CompoundFormat#printTextBeside
    * @see FormatBlock#printTextBeside
		* @see printEndOfFormat
    */
  public void printBreaks(int lines) {

		String text = line.toString();

		if (wrapAround)
			while (text.length() > 0) {
				if (text.length() > width) {
					output.println(text.substring(0,width-1)+"\\");
					text = text.substring(width-1);
				} else {
					output.print(text);
					break;
				}
			}
		else
			output.print(text);

		line.setLength(0);

    spaceWidth = 0;

		for (int i = lines; i-->0; )
			output.println();

		// output.flush();
  }

  /**
    * This method is called for Strings to be printed. It first appends
    * the accumulated spaces (if not at the beginning of a line) or the
		* given indentation (if at beginning of a line) to the current line
    * before it adds the actual text.
    *
    * @param indentation how far shall the text be indented, if at the
    * beginning of a line
    * @param text the string to be printed
    *
    * @see FormatText#printTextBeside
    */

  public void printText(int indentation, String text) {

    // at the beginning of a line?
    if (atLineBegin()) { 
      // print out the indentation of the last new line
      if (indentation > 0){
        line.append(getSpaces(indentation));
      }
    } else {
			if (spaceWidth > 0) {
				// print the accumulated spaces
				line.append(getSpaces(spaceWidth));

				spaceWidth = 0;
			}

			int l = line.length();
			int i = indentation-l;
			if (i > 0){
			  line.append(getSpaces(i));
			}
		}

		line.append(text);
  }

  /** A cache for representing spaces. */
  private static Vector spaceCache = new Vector();
  private static String getSpaces(int num){
    if (num < 0) num = 0;
    int s = spaceCache.size();
    if (num < s){
      return (String)spaceCache.elementAt(num);
    }
    for (int i = s; i <= num; i++){
      char[] buf = new char[i];
      for (int j = 0; j < i; j++) buf[j] = ' ';
      spaceCache.addElement(new String(buf));
    }
    return (String)spaceCache.elementAt(num);
  }


  /**
    * This method wraps up the printing process. It is called by the
    * outermost Format to be printed after the Format has been printed.
    * If there are still characters in the current line that haven't been
    * printed, yet, they are printed by this method, followed by a newline.
    *
    * @see Format#printFormat
    */
  public void printEndOfFormat() {
		if (!atLineBegin())
			printBreaks(1);
		output.flush();
  }
}
