/**
 * Mutable long object.
 * 
 * @author Ashkan Moatamed
 */
public class MutableLong extends Number implements Comparable<MutableLong> {
	/**
	 * Eclipse automatically generated serial version UID.
	 */
	private static final long serialVersionUID = -3922068836463903832L;

	private long value;

	/**
	 * Default ctor.
	 */
	public MutableLong() {
		this.value = 0;
	}

	/**
	 * Construct a new MutableLong object with the given value.
	 * 
	 * @param value
	 *            the given value
	 */
	public MutableLong(long value) {
		this.value = value;
	}

	/**
	 * Copy ctor.
	 * 
	 * @param other
	 *            the given MutableLong object
	 * 
	 * @throws NullPointerException
	 *             If <code>other == null</code>
	 */
	public MutableLong(MutableLong other) throws NullPointerException {
		this.value = other.value;
	}

	/**
	 * @return <code>this.value</code>.
	 */
	public long get() {
		return this.value;
	}

	/**
	 * Set <code>this.value</code> to the given long and return the old value.
	 * 
	 * @param value
	 *            the given value
	 * 
	 * @return The old value.
	 */
	public long set(long value) {
		final long oldValue = this.value;
		this.value = value;
		return oldValue;
	}

	@Override
	public int intValue() {
		return (int) this.value;
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
		return Long.toString(this.value);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (int) (this.value ^ (this.value >>> 32));
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		return ((obj instanceof MutableLong) ? (this.value == ((MutableLong) obj).value) : false);
	}

	/**
	 * @param other
	 *            the given MutableLong object
	 * 
	 * @return <code>(other == null) ? false : (this.value == other.value)</code>.
	 * 
	 * @see #equals(Object)
	 */
	public boolean equals(MutableLong other) {
		return ((other == null) ? false : (this.value == other.value));
	}

	@Override
	public int compareTo(MutableLong other) throws NullPointerException {
		return Long.compare(this.value, other.value);
	}
}
