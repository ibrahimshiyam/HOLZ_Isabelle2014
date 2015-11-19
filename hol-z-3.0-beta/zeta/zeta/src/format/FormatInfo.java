package zeta.format;

import java.util.Hashtable;

/**
 * Instances of the FormatInfo class are used in the process of
 * formatting with the <code>Format.buildFormat</code> method. They
 * are used to detect sharing and cylcles in object structures.
 *
 *
 * @see Format#buildFormat
 * @see Formattable
 *
 * @author Jacob Wieland (ughosage@cs.tu-berlin.de)
 * @version $Id: FormatInfo.java,v 1.1.1.1 1998/09/01 10:51:13 wg Exp $
 */

public class FormatInfo {

  /**
   * Return an object identity code.
   */
  private static Integer code(Object ob){
    if (ob == null)
      return new Integer(0);
    else
      return new Integer(System.identityHashCode(ob));
  }
  
  /**
   * Fields.
   */
  private Hashtable visited = new Hashtable(100);
  private Hashtable generalTypes = new Hashtable(100);
  private Class ObjectClass = Object.class;

  /**
   * Test whether the given object has been visited before with
   * this FormatInfo.
   */
  public boolean visited(Object ob) {
    return visited.containsKey(code(ob));
  }

  /**
   * Return a format for representing a label of a previously
   * visited object. 
   */
  public Format getLabel(Object ob){
    return Format.literal("<" + visitNumber(ob) + "<");
  }

  /**
   * Visit the given object the first time, generating 
   * a label for it and returnings its format.
   */
  public Format visitAndGetLabel(Object ob){
    return Format.literal("<" + visit(ob) + "<");
  }

  /**
   * Access to the number of a label of visited object.
   */
  public int visitNumber(Object ob) {
    return ((Integer)visited.get(code(ob))).intValue();
  }

  /** 
   * Visit the given object and return its label number.
   */
  public int visit(Object ob) {
    Integer c = code(ob);
    if (visited.containsKey(c)){
      return ((Integer)visited.get(c)).intValue();
    }

    int n = visited.size() + 1;
    visited.put(c,new Integer(n));

    return n;
  }

  /**
   * Remove the given object from the set of visited objects.
   * The next time it is formatted it will be treated has if it
   * had never been seen before.
   */
  public void unvisit(Object ob){
    visited.remove(code(ob));
  }


  /**
   * Assign a general type to the given object. This is used
   * by the internal generic format functions.
   */
  public void addGeneralType(Object ob, Class type) {
    if (ob != null && type != ObjectClass) {
      // only _one_ general type is allowed at any one time
      // some objects coule be part of several other objects/arrays
      // and thus have several general types (dependent on the context)
      Integer c = code(ob);
      if (generalTypes.containsKey(c))
	generalTypes.remove(c);
      generalTypes.put(c,type);
    }
  }

  /**
   * Retrieve the general type of an object. Used by the internal
   * generic format functions.
   */
  public Class generalType(Object ob) {
    Integer c = code(ob);
    if (generalTypes.containsKey(c))
      return (Class)generalTypes.get(c);
    else
      return ObjectClass;
  }

}
