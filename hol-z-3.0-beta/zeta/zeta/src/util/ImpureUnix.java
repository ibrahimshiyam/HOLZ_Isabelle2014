package zeta.util;

/** 
 * This class provides the implementation of system dependend
 * functionality under Unix. 
 */

import java.util.Date;
import java.io.File;

import zeta.util.*;

public class ImpureUnix extends Impure {

  static {
    /*
    try {
       System.loadLibrary("ZetaUnix");
    } 
    catch (UnsatisfiedLinkError e) {
       throw new FatalError(
		   "cannot load Unix library (libZetaUnix.so).");
   
    }
    */
  }

  /** */
  public Date lastModified(File file) {
    // Under Linux at least, the value of lastModified seems to be
    // milliseconds since Jan 1, 1970. So we can do it as below.
    // FIXME: check for Solaris
    return file.isFile() ? new Date(file.lastModified()) : new Date();
  }

  /** */
  public synchronized void catchInterrupts(){}

  /** */
  public synchronized int readAndClearInterrupts(){ return 0; }
  
  // /** */
  // public synchronized native void catchInterrupts();

  // /** */
  // public synchronized native int readAndClearInterrupts();
  

}
