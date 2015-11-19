package zeta.format;

/**
  * This interface, if implemented by a class, indicates that a custom
  * method <code>toFormat</code> for formatting is provided. The
  * method for building a format,
  * <code>Format.buildFormat</code>, uses this method for formatting
  * an object if it is provided.  <p>
  *
  * The custom method takes as a parameter a data object which may
  * be used to detect cycles and sharing in object structures. <p>
  *
  * Here is an example of an implementation of <code>toFormat</code>
  * with sharing detection:
  *
  <pre>
  public Format toFormat(FormatInfo info){
    if (info.visited(this))
      // return just a label reference for this object
      return info.getLabel(this);
    else 
      return block(info.visitAndGetLabel(this),
                   Format.buildFormat(info, field1),
		   ...,
                   Format.buildFormat(info, fieldn));
  }
  </pre>
  *
  * @see Format#buildFormat
  * @see FormatInfo
  * @author Jacob Wieland (ughosage@cs.tu-berlin.de) 
  * @version $Id: Formattable.java,v 1.1.1.1 1998/09/01 10:51:13 wg Exp $
  */

public interface Formattable {

  /**
   * Convert this object to a format.
   *
   * @param info An information object of type FormatInfo containing
   * information about the Format context of this object
   * (like already visited objects to prevent recursions). 
   * 
   * @return A Format object to be used for pretty printing the contents
   * of this object.
   *
   * @see Format
   * @see FormatInfo
   *
   */
  public Format toFormat(FormatInfo info);

}
