package zeta.agl;

/** Some hacks written in Java to work around Pizzas special
    treatment of arrays. */

import java.lang.Class;
import java.lang.reflect.Array;
import pizza.support.array;


class ArrayHacks {

  /** Allocate a Pizza object array of given 
    * size holding elements of given class. This cannot
    * performed in Pizza since the compiler would detect
    * the class array and implicitely insert a toObject() call. */
  static Object allocArray(int size, Class cls) {
    return array.fromObject(Array.newInstance(cls, size));
  }


  /** Test whether given object is an instance of a Java array,
    * Object[].  This cannot performed in Pizza since Object[] would
    * be treated as a Pizza array. */
  static boolean isObjectArray(Object a){
    return a instanceof Object[];
  }
  
  /** Read the given Pizza array. Necessary since pizza.support
   * currently does not implements the Serializable interface.
   */
  static Object readArray(java.io.ObjectInputStream in)
  throws java.io.IOException, ClassNotFoundException {
    return array.fromObject(in.readObject());
  }

}
	
