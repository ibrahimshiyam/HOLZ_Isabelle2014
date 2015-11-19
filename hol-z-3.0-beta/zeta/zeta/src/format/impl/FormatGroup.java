package zeta.format.impl;

import java.lang.System;
import zeta.format.*;

/**
  * This is a specialization of the class FormatBeside for a list of Formats
  * that should be grouped in a way that the first item is printed 'beside'
  * the 2nd item and the last item is printed 'beside' the one before that.
  * </p>
  * This behaviour is especially useful for bracketed constructions.
  * </p>
  * Here an example:
  <pre>
   ________________.....
  |___|            |   :
  :   |            |___:
  :...|____________|___|
  </pre>
  * @see FormatBeside
  *
  * @author Jacob Wieland (ughosage@cs.tu-berlin.de)
  */
public class FormatGroup extends FormatBeside {

  private static Format[] makeFormatGroup(Format[] formats) {
    Format[] f;

    if (formats.length > 3) {
      int leftSpaces = 0, rightSpaces = 0;
      int l = formats.length;
      // count spaces between left bracket and inner block
      for (int i = 1; i < l - 2; i++)
        if (formats[i] instanceof FormatSpace)
          leftSpaces++;
        else
          break;
      // now count the spaces between inner block and right bracket
      for (int i = l - 2; i > leftSpaces + 1; i--)
        if (formats[i] instanceof FormatSpace)
          rightSpaces++;
        else
          break;

      int innerLength = l - (leftSpaces+rightSpaces+2);
      f = new Format[leftSpaces+rightSpaces+3]; // spaces + brackets + inner
      Format[] sub = new Format[innerLength];
      System.arraycopy(formats,0,f,0,leftSpaces+1);
      System.arraycopy(formats,leftSpaces+1,sub,0,innerLength);
      f[leftSpaces+1] = new FormatLine(sub);
      System.arraycopy(formats,l-(rightSpaces+1),f,leftSpaces+2,rightSpaces+1);
    } else {
      f = formats;
    }
    return f;
  }

  public FormatGroup(int indentation, Format[] formats) {
    super(indentation,FormatGroup.makeFormatGroup(formats));
  }

  public FormatGroup(Format[] formats) {
    super(FormatGroup.makeFormatGroup(formats));
  }
 
}
