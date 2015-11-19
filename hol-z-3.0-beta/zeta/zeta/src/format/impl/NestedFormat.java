package zeta.format.impl;

/**
  * This abstract class is an extension of the abstract class Format
  * and is to be inherited by all Format classes that wish to be able
  * to have an indentation of their own (like all complex Formats and
  * FormatText).
  *
  * This indentation is added to the indentation that is given to the
  * printer whenever this Format shall be printed in a new line.
  *
  * If a format is printed 'beside' another format, i.e. the printer doesn't
  * start to print it in a new line, then this additional indentation is
  * ignored.
  *
  * @author Jacob Wieland (ughosage@cs.tu-berlin.de)
  *
  * @see Format
  * @see CompoundFormat
  * @see FormatText
  */
import zeta.format.*;
public abstract class NestedFormat extends Format {
  //private
  public int nesting;

	/**
		* @return nesting of the block initialized by the constructor
		*/
	public int nesting() {
		return nesting;
	}

  /**
    * The constructor sets the indentation of this Format.
    *
    * @param indentation how much indentation shall be added to the already
    * given indentation at the beginning of a line.
    */
  public NestedFormat(int indentation) {
    super();
    nesting = indentation;
  }

  public NestedFormat nested(int nesting) {
    this.nesting = nesting;
    return this;
  }
}
