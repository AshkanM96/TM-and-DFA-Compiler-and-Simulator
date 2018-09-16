/**
 * Mutable integer object.
 * 
 * @author Ashkan Moatamed
 */
public class MutableInteger extends Number implements Comparable<MutableInteger> {
	/**
	 * Eclipse automatically generated serial version UID.
	 */
	private static final long serialVersionUID = 7034951900087644980L;

	private int value;

	/**
	 * Default ctor.
	 */
	public MutableInteger() {
		this.value = 0;
	}

	/**
	 * Construct a new MutableInteger object with the given value.
	 * 
	 * @param value
	 *            the given value
	 */
	public MutableInteger(int value) {
		this.value = value;
	}

	/**
	 * Copy ctor.
	 * 
	 * @param other
	 *            the given MutableInteger object
	 * 
	 * @throws NullPointerException
	 *             If <code>other == null</code>
	 */
	public MutableInteger(MutableInteger other) throws NullPointerException {
		this.value = other.value;
	}

	/**
	 * @return <code>this.value</code>.
	 */
	public int get() {
		return this.value;
	}

	/**
	 * Set <code>this.value</code> to the given int and return the old value.
	 * 
	 * @param value
	 *            the given value
	 * 
	 * @return The old value.
	 */
	public int set(int value) {
		final int oldValue = this.value;
		this.value = value;
		return oldValue;
	}

	@Override
	public int intValue() {
		return this.value;
	}

	@Override
	public long longValue() {
		return this.value;
	}

	@Override
	public float floatValue() {
		return this.value;
	}

	@Override
	public double doubleValue() {
		return this.value;
	}

	@Override
	public String toString() {
		return Integer.toString(this.value);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + this.value;
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		return ((obj instanceof MutableInteger) ? (this.value == ((MutableInteger) obj).value) : false);
	}

	/**
	 * @param other
	 *            the given MutableInteger object
	 * 
	 * @return <code>(other == null) ? false : (this.value == other.value)</code>.
	 * 
	 * @see #equals(Object)
	 */
	public boolean equals(MutableInteger other) {
		return ((other == null) ? false : (this.value == other.value));
	}

	@Override
	public int compareTo(MutableInteger other) throws NullPointerException {
		return Integer.compare(this.value, other.value);
	}
}
