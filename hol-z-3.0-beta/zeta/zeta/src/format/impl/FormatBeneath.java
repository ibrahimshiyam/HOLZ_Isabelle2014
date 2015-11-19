package zeta.format.impl;

/**
  * This is a compound Format class for component Format texts that should
  * be printed beneath each other. Thus, it has exactly the default behaviour
  * as described under CompoundFormat (see there).
  *
  * @author Jacob Wieland (ughosage@cs.tu-berlin.de)
  *
  * @see CompoundFormat
  * @see Format
  */

import java.io.PrintWriter;
import zeta.format.*;

public class FormatBeneath extends CompoundFormat {

  public FormatBeneath(int indentation, Format[] formats) {
    super(indentation,formats);
  }

  public FormatBeneath(Format[] formats) {
    super(formats);
  }

  /* Convenience constructors: */
  public FormatBeneath(int indent, Format f1, Format f2) {
    this(indent, new Format[] { f1, f2 });
  }
  public FormatBeneath(int indent, Format f1, Format f2, Format f3) {
    this(indent, new Format[] { f1, f2, f3 });
  }
  public FormatBeneath(int indent, Format f1, Format f2, Format f3, Format f4) {
    this(indent, new Format[] { f1, f2, f3, f4 });
  }
  public FormatBeneath(Format f1, Format f2) {
    this(new Format[] { f1, f2 });
  }
  public FormatBeneath(Format f1, Format f2, Format f3) {
    this(new Format[] { f1, f2, f3 });
  }
  public FormatBeneath(Format f1, Format f2, Format f3, Format f4) {
    this(new Format[] { f1, f2, f3, f4 });
  }
  public FormatBeneath(int indent, Format f1, Format f2, Format f3, 
		      Format f4, Format f5) 
  {
    this(indent, new Format[] { f1, f2, f3, f4, f5 });
  }
  public FormatBeneath(Format f1, Format f2, Format f3, Format f4, Format f5) {
    this(new Format[] { f1, f2, f3, f4, f5 });
  }
  public FormatBeneath(int indent, Format f1, Format f2, Format f3, 
		      Format f4, Format f5, Format f6) {
    this(indent, new Format[] { f1, f2, f3, f4, f5, f6 });
  }
  public FormatBeneath(Format f1, Format f2, Format f3, Format f4, Format f5,
                      Format f6) 
  {
    this(new Format[] { f1, f2, f3, f4, f5, f6 });
  }

  protected int computeMaxWidth() {
    int usedWidth;
    int maxUsedWidth = 0;
    int l = formats.length;

    for (int i = 0; i < l; i++) {
      if ((usedWidth = formats[i].maxWidth()) > maxUsedWidth)
        maxUsedWidth = usedWidth;
    }

    return maxUsedWidth;
  }

  protected int computeMaxLastWidth() {
    int l = formats.length;

    if (l > 0)
      return formats[l-1].maxLastWidth();
    return 0;
  }

  protected int computeMinHeight() {
    int usedHeight = 0;

    for (int i = formats.length; i-->0; ) {
			if (formats[i] instanceof FormatSpace)
				continue;
      usedHeight += formats[i].minHeight();
    }

    return usedHeight;
  }

  /** */
  public void dumpText(PrintWriter writer){
    for (int i = 0; i < formats.length; i++){
      formats[i].dumpText(writer);
      writer.println();
    }
  }
}
