package zeta.format.impl;

import zeta.format.*;

public class FormatList extends Object {
	private Format[] array;
	private int index;

	public FormatList(int length) {
		super();
		array = new Format[length];
		index = 0;
	}

	public FormatList add(Format f) {
		if (index < array.length) {
			array[index] = f;
			index++;
		}
		return this;
	}

	public Format[] toArray() { return array; }
}
