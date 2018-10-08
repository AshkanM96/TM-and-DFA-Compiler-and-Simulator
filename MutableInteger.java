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

	/**
	 * The object's primitive value.
	 */
	private int value;

	/**
	 * Default ctor.
	 */
	public MutableInteger() {
		this.value = 0;
	}

	/**
	 * Construct a MutableInteger object with the given value.
	 * 
	 * @param other
	 *            the given int value
	 */
	public MutableInteger(int other) {
		this.value = other;
	}

	/**
	 * Construct a MutableInteger object with the given value.
	 * 
	 * @param other
	 *            the given Integer value
	 * 
	 * @throws NullPointerException
	 *             If <code>other == null</code>
	 */
	public MutableInteger(Integer other) throws NullPointerException {
		this.value = other.intValue();
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

	/**
	 * @param other
	 *            the given Integer object
	 * 
	 * @return <code>(other == null) ? false : (this.value == other.intValue())</code>.
	 * 
	 * @see #equals(Object)
	 */
	public boolean equals(Integer other) {
		return ((other == null) ? false : (this.value == other.intValue()));
	}

	/**
	 * @param other
	 *            the given int value
	 * 
	 * @return <code>this.value == other</code>.
	 * 
	 * @see #equals(Object)
	 */
	public boolean equals(int other) {
		return (this.value == other);
	}

	@Override
	public int compareTo(MutableInteger other) throws NullPointerException {
		return Integer.compare(this.value, other.value);
	}

	/**
	 * @param other
	 *            the given Integer object
	 * 
	 * @return <code>Integer.compare(this.value, other.intValue())</code>.
	 * 
	 * @throws NullPointerException
	 *             If <code>other == null</code>
	 * 
	 * @see #compareTo(MutableInteger)
	 */
	public int compareTo(Integer other) throws NullPointerException {
		return Integer.compare(this.value, other.intValue());
	}

	/**
	 * @param other
	 *            the given int value
	 * 
	 * @return <code>Integer.compare(this.value, other)</code>.
	 * 
	 * @see #compareTo(MutableInteger)
	 */
	public int compareTo(int other) {
		return Integer.compare(this.value, other);
	}
}
