package zeta.format.impl;
import zeta.format.*;

public class TextRectangle {
  public int width, height, lastWidth;

  public TextRectangle(int width, int height, int lastWidth) {
    this.width = width;
    this.height = height;
    this.lastWidth = lastWidth;
  }

  // A text-rectangle that only covers one line
  public TextRectangle(int width) {
    this(width,1,width);
  }

  public TextRectangle nested(int indentation) {
    width += indentation;
    lastWidth += indentation;
    return this;
  }
}
