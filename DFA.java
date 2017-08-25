import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Scanner;
import java.util.regex.Pattern;

public class DFA {
	/*
	 * for simplicity, all methods only throw IllegalArgumentException so that only one type of
	 * exception need be handled but in general, it's better practice to throw other types of exceptions
	 * when appropriate such as NullPointerException, IllegalStateException and etc.
	 */

	public static final char DELIMITER_CHAR = ' ';
	public static final String DELIMITER_STRING = Character.toString(DFA.DELIMITER_CHAR);

	public static final int MIN_NUM_STATES = 1, MAX_NUM_STATES = 10000, MIN_INPUT_ALPHABET_SIZE = 1,
			MAX_INPUT_ALPHABET_SIZE = 1000;
	private int numStates, inputAlphabetSize;
	// inputIndex maps inputCharacters to indices
	private HashMap<String, Integer> inputIndex;
	private String[] inputAlphabet;

	public static final String WHITESPACE_REGEX = "(\\s)+";
	private static final Pattern WHITESPACE_PATTERN = Pattern.compile(DFA.WHITESPACE_REGEX);

	private int numAcceptingStates;
	// accepting holds which states are accepting states
	private boolean[] accepting;
	// next[i][j] = delta(state i, input char at index j)
	private int[][] nextState;
	// array used to keep track of defined transitions
	private boolean[][] defined;
	private int totalNumTransitions, numDefinedTransitions;
	private int[] stateNumDefined;
	/*
	 * run is used to determine whether this instance actually needs to be run on a testString or if the
	 * result of any run is already known due to the special nature of the given machine description
	 */
	private boolean run;

	public static final String DEFAULT = "default";

	public static final int DEFAULT_MAX_STRING_COUNT = 1000, MAX_STRINGS_COUNT = 100000;
	private int maxStringCount, actualStringCount, acceptCount, rejectCount;
	/*
	 * count holds whether maxStringCount is greater than 1 or not so that the boolean is not
	 * reevaluated every time that it is needed. checkStringsCount is used to determine when to estimate
	 * the number of strings to test(stringsCount) so that the time consuming process isn't repeatedly
	 * performed by the testString length mutator methods
	 */
	private boolean count, checkStringsCount = true;
	/*
	 * maps testString to accept:stepCount. always construct results with initialCapacity of
	 * maxStringCount so that the need for resizing, rehashing, ... is greatly reduced
	 */
	private HashMap<ArrayList<Integer>, String> results;

	public static final int DEFAULT_MIN_LENGTH = 0, DEFAULT_MAX_LENGTH = 4;
	private int minLength, maxLength;

	public static final String DEFAULT_INITIAL_STRING = "";
	private static final ArrayList<Integer> DEFAULT_INITIAL_ARRAY = new ArrayList<Integer>();
	private String initialString;
	private ArrayList<Integer> initialArray = DFA.DEFAULT_INITIAL_ARRAY;

	private boolean isScanning, isConstructing, isSimulating;

	public static final boolean DEFAULT_INCLUDE_COMMENTS = true;
	private boolean includeComments;
	private StringBuilder comments;

	// cause is the message of the last exception thrown by this instance
	private String cause;
	/*
	 * staticCause is the message of the last exception thrown by one of the static methods or the
	 * constructors
	 */
	private static String staticCause;
	private int lineNumber;

	/*
	 * OR strChange with itself so that it's not set to false if it's already true. Put the more
	 * complicated expression on the right side of the or(||) so that if strChange is already true, the
	 * expression isn't evaluated due to compiler short-circuiting so that time is saved
	 */
	private boolean strChange, comChange;
	private String savedStr, savedCom;

	public static final int LINE_1_NUM_ENTRIES = 4, COMMAND_LINE_MAX_NUM_ENTRIES = 4;

	public static final int SECONDS_PER_DAY = 86400, SECONDS_PER_HOUR = 3600, SECONDS_PER_MINUTE = 60,
			MILLISECONDS_PER_SECOND = 1000, NANOSECONDS_PER_MILLISECOND = 1000000;
	private String time;

	public static final String DEFAULT_FILE_NAME = "machine";
	private HashMap<String, String> machines = new HashMap<String, String>();
	private static int machineCount;
	private boolean overwrote;
	public static final String SAVE = "save", STDIN = "stdin", TRUE_1 = "t", TRUE_2 = "true", FALSE_1 = "f",
			FALSE_2 = "false";

	public int getNumStates() {
		return this.numStates;
	}

	@SuppressWarnings("null")
	public int setNumStates(int numStates, boolean copyValidTransitions) throws IllegalArgumentException {
		if (this.getNumStates() == this.validateNumStates(numStates)) {
			return this.getNumStates();
		}

		int prevNumStates = this.getNumStates(), n = this.getNumStates(), s = this.getInputAlphabetSize();
		boolean[] accepting = null;
		int[][] next = null;
		boolean[][] defined = null;

		if (copyValidTransitions) {
			accepting = new boolean[n];
			next = new int[n][s];
			defined = new boolean[n][s];
			for (int i = 0; i < n; i++) {
				accepting[i] = this.accepting[i];
				for (int j = 0; j < s; j++) {
					next[i][j] = this.nextState[i][j];
					defined[i][j] = this.defined[i][j];
				}
			}
		}

		n = this.numStates = numStates;
		this.numAcceptingStates = 0;
		this.accepting = new boolean[n];
		this.totalNumTransitions = n * s;
		this.stateNumDefined = new int[n];
		this.initializeTransitions();

		if (copyValidTransitions) {
			int min = Math.min(n, prevNumStates);

			for (int i = 0; i < n; i++) {
				if ((i < prevNumStates) && accepting[i]) {
					this.accepting[i] = true;
					this.numAcceptingStates++;
				}

				for (int j = 0; j < s; j++) {
					// increase in number of states
					if (min == prevNumStates) {
						// copy transition only if initial state existed
						if (i < prevNumStates) {
							this.nextState[i][j] = next[i][j];
							if (defined[i][j]) {
								this.defined[i][j] = true;
								this.numDefinedTransitions++;
							}
						}
					} else { // decrease in number of states
						int state = next[i][j];
						// copy transition only if final state is still valid
						if (state < n) {
							this.nextState[i][j] = state;
							if (defined[i][j]) {
								this.defined[i][j] = true;
								this.numDefinedTransitions++;
							}
						}
					}
				}
			}
		}

		this.resetRun();
		return this.getNumStates();
	}

	public int setNumStates(int numStates) throws IllegalArgumentException {
		return this.setNumStates(numStates, false);
	}

	public static boolean isValidNumStates(int numStates) {
		return (numStates >= DFA.MIN_NUM_STATES && numStates <= DFA.MAX_NUM_STATES);
	}

	public static String getNumStatesRange() {
		return ('[' + DFA.MIN_NUM_STATES + ", " + DFA.MAX_NUM_STATES + ']');
	}

	public int validateNumStates(int numStates) throws IllegalArgumentException {
		if (!DFA.isValidNumStates(numStates)) {
			this.cause = "Given number of states(" + numStates + ") isn't in the range of " + DFA.getNumStatesRange()
					+ '.';
			this.illegalArg();
		}
		return numStates;
	}

	public int getMaxState() {
		return (this.getNumStates() - 1);
	}

	public boolean isValidState(int state) {
		return (state >= 0 && state <= this.getMaxState());
	}

	public String getStateRange() {
		return ("[0, " + this.getMaxState() + ']');
	}

	public int validateState(int state, boolean isInitial) throws IllegalArgumentException {
		if (!this.isValidState(state)) {
			this.cause = "Given " + (isInitial ? "initial" : "final") + " state";
			if (this.isScanning) {
				this.cause += " on line " + this.lineNumber;
			}
			this.cause += '(' + state + ") isn't in the range of " + this.getStateRange() + '.';
			this.illegalArg();
		}
		return state;
	}

	public int validateState(int state) throws IllegalArgumentException {
		return this.validateState(state, true);
	}

	public int getInputAlphabetSize() {
		return this.inputAlphabetSize;
	}

	public int getMaxInputIndex() {
		return (this.getInputAlphabetSize() - 1);
	}

	public boolean isValidInputCharIndex(int index) {
		return (index >= 0 && index <= this.getMaxInputIndex());
	}

	public String getInputCharIndexRange() {
		return ("[0, " + this.getMaxInputIndex() + ']');
	}

	public int validateInputCharIndex(int index) throws IllegalArgumentException {
		if (!this.isValidInputCharIndex(index)) {
			this.cause = "Given input character index(" + index + ") isn't in the range of "
					+ this.getInputCharIndexRange() + '.';
			this.illegalArg();
		}
		return index;
	}

	public boolean isValidInputChar(String s) {
		if (s == null || DFA.WHITESPACE_PATTERN.matcher(s).find()) {
			return false;
		}
		return this.inputIndex.containsKey(s);
	}

	public int inputCharIndexOf(String s) {
		Integer index = this.inputIndex.get(s);
		return (index != null ? index : -1);
	}

	public int validateInputChar(String s) throws IllegalArgumentException {
		int index = this.inputCharIndexOf(s);
		if (index == -1) {
			this.cause = "Given input character";
			if (this.isScanning) {
				this.cause += " on line " + this.lineNumber;
			}
			this.cause += '(' + s + ") isn't a valid input character.";
			this.illegalArg();
		}
		return index;
	}

	public String getInputChar(int index) throws IllegalArgumentException {
		return this.inputAlphabet[this.validateInputCharIndex(index)];
	}

	public String[] getInputAlphabet() {
		String[] result = new String[this.getInputAlphabetSize()];
		System.arraycopy(this.inputAlphabet, 0, result, 0, result.length);
		return result;
	}

	public static String[] getDefaultInputAlphabet() {
		String[] inputAlphabet = { "0", "1" };
		return inputAlphabet;
	}

	public int getNumAcceptingStates() {
		return this.numAcceptingStates;
	}

	public boolean getAccepting(int state) throws IllegalArgumentException {
		if (!this.isValidState(state)) {
			this.cause = "Given state(" + state + ") isn't in the range of " + this.getStateRange() + '.';
			this.illegalArg();
		}
		return this.accepting[state];
	}

	public boolean[] getAccepting() {
		boolean[] result = new boolean[this.getNumStates()];
		System.arraycopy(this.accepting, 0, result, 0, result.length);
		return result;
	}

	public int setAcceptingState(int state, boolean accepting) throws IllegalArgumentException {
		if (!this.isValidState(state)) {
			this.cause = "Given state(" + state + ") isn't in the range of " + this.getStateRange() + '.';
			this.illegalArg();
		} else if (this.accepting[state] == accepting) {
			return state;
		}

		this.accepting[state] = accepting;
		this.numAcceptingStates += accepting ? 1 : -1;
		this.resetRun();
		this.strChange = true;
		return state;
	}

	public boolean[] setAccepting(int numAcceptingStates, int[] acceptingStates) throws IllegalArgumentException {
		boolean[] accepting = this.validateAccepting(numAcceptingStates, acceptingStates);
		System.arraycopy(accepting, 0, this.accepting, 0, (this.numAcceptingStates = numAcceptingStates));
		this.resetRun();
		this.strChange = true;
		return accepting;
	}

	@SuppressWarnings("null")
	public boolean[] validateAccepting(int numAcceptingStates, int[] acceptingStates) throws IllegalArgumentException {
		if (acceptingStates == null || acceptingStates.length != this.validateNumAcceptingStates(numAcceptingStates)) {
			this.cause = "Given accepting states array isn't valid.";
			this.illegalArg();
		}

		Arrays.sort(acceptingStates);
		boolean[] accepting = new boolean[this.getNumStates()];
		for (int i = 0; i < numAcceptingStates; i++) {
			int acceptState = acceptingStates[i];
			if (!this.isValidState(acceptState)) {
				this.cause = "Given accept state index(" + acceptState + ") isn't in the range of "
						+ this.getStateRange() + '.';
				this.illegalArg();
			} else if (accepting[acceptState]) {
				this.cause = "State " + acceptState + " has been defined to be an accept state more than once.";
				this.illegalArg();
			}
			accepting[acceptState] = true;
		}
		return accepting;
	}

	public boolean isValidNumAcceptingStates(int numAcceptingStates) {
		return (numAcceptingStates >= 0 && numAcceptingStates <= this.getNumStates());
	}

	public String getNumAcceptingStatesRange() {
		return ("[0, " + this.getNumStates() + ']');
	}

	public int validateNumAcceptingStates(int numAcceptingStates) throws IllegalArgumentException {
		if (!this.isValidNumAcceptingStates(numAcceptingStates)) {
			this.cause = "Given number of accepting states(" + numAcceptingStates + ") isn't in the range of "
					+ this.getNumAcceptingStatesRange() + '.';
			this.illegalArg();
		}
		return numAcceptingStates;
	}

	public int[] getAcceptingStates() {
		int[] result = new int[this.getNumAcceptingStates()];
		int index = 0;
		for (int i = 0; i < this.getNumStates(); i++) {
			if (this.accepting[i]) {
				result[index++] = i;
			}
		}
		return result;
	}

	public Object[] setAlphabet(int inputAlphabetSize, String[] inputAlphabet) throws IllegalArgumentException {
		inputAlphabet = this.validateAlphabet(inputAlphabetSize, inputAlphabet);
		this.inputAlphabet = new String[this.inputAlphabetSize = inputAlphabetSize];
		System.arraycopy(inputAlphabet, 0, this.inputAlphabet, 0, inputAlphabetSize);

		this.inputIndex = new HashMap<String, Integer>(inputAlphabetSize);
		for (int i = 0; i < inputAlphabetSize; i++) {
			this.inputIndex.put(this.inputAlphabet[i], i);
		}

		this.totalNumTransitions = this.getNumStates() * inputAlphabetSize;
		this.initializeTransitions();
		this.resetRun();

		Object[] result = { null, null, null, this.results }, r = this.getInitialStringRepresentations();
		System.arraycopy(r, 0, result, 0, r.length);
		try {
			this.setInitialArray(this.initialArray, false);
		} catch (IllegalArgumentException ex) {
			this.setInitialArray(this.getMinArray(), false);
		}
		this.results = new HashMap<ArrayList<Integer>, String>(this.getMaxStringCount());
		return result;
	}

	public boolean isValidAlphabet(int inputAlphabetSize, String[] inputAlphabet) {
		try { // if no exception is thrown then the result is necessarily true
			return (this.validateAlphabet(inputAlphabetSize, inputAlphabet) != null);
		} catch (IllegalArgumentException ex) {
			return false;
		}
	}

	@SuppressWarnings("null")
	public String[] validateAlphabet(int inputAlphabetSize, String[] inputAlphabet) throws IllegalArgumentException {
		this.validateInputAlphabetSize(inputAlphabetSize);
		if (inputAlphabet == null || inputAlphabet.length != inputAlphabetSize) {
			this.cause = "Given input alphabet isn't valid.";
			this.illegalArg();
		}

		HashMap<String, Integer> inputIndex = new HashMap<String, Integer>();
		String inputChar;
		for (int i = 0; i < inputAlphabetSize; i++) {
			if ((inputChar = inputAlphabet[i]) == null) {
				this.cause = "Given input alphabet isn't valid since it contains null at index " + i + '.';
				this.illegalArg();
			} else if (inputChar.isEmpty()) {
				this.cause = '"' + inputChar + "\" isn't valid since it's the empty string.";
				this.illegalArg();
			} else if (DFA.WHITESPACE_PATTERN.matcher(inputChar).find()) {
				this.cause = '"' + inputChar + "\" isn't valid since it contains whitespace.";
				this.illegalArg();
			} else if (inputIndex.containsKey(inputChar)) {
				this.cause = '"' + inputChar + "\" has been defined more than once.";
				this.illegalArg();
			}
			inputIndex.put(inputChar, i);
		}

		Arrays.sort(inputAlphabet);
		this.validateInputAlphabet(inputAlphabet);
		return inputAlphabet;
	}

	public static boolean isValidInputAlphabetSize(int inputAlphabetSize) {
		return (inputAlphabetSize >= DFA.MIN_INPUT_ALPHABET_SIZE && inputAlphabetSize <= DFA.MAX_INPUT_ALPHABET_SIZE);
	}

	public static String getInputAlphabetSizeRange() {
		return ('[' + DFA.MIN_INPUT_ALPHABET_SIZE + ", " + DFA.MAX_INPUT_ALPHABET_SIZE + ']');
	}

	public int validateInputAlphabetSize(int inputAlphabetSize) throws IllegalArgumentException {
		if (!DFA.isValidInputAlphabetSize(inputAlphabetSize)) {
			this.cause = "Given input alphabet size(" + inputAlphabetSize + ") isn't in the range of "
					+ DFA.getInputAlphabetSizeRange() + '.';
			this.illegalArg();
		}
		return inputAlphabetSize;
	}

	public static boolean isValidInputAlphabet(String[] s) {
		if (s == null || s.length == 0) {
			return false;
		}

		for (int i = 0; i < s.length; i++) {
			if (s[i] == null) {
				return false;
			}
		}

		String shorter, longer;
		for (int i = 0; i < s.length; i++) {
			for (int j = i + 1; j < s.length; j++) {
				shorter = s[i];
				longer = s[j].substring(0, s[i].length());
				if (s[i].length() > s[j].length()) {
					shorter = s[j];
					longer = s[i].substring(0, s[j].length());
				}
				if (shorter.equals(longer)) {
					return false;
				}
			}
		}

		return true;
	}

	public String[] validateInputAlphabet(String[] s) throws IllegalArgumentException {
		if (!DFA.isValidInputAlphabet(s)) {
			this.cause = "Given input alphabet isn't valid since two of its characters start the same way.";
			this.illegalArg();
		}
		return s;
	}

	private Object[] getInitialStringRepresentations() {
		Object[] result = { this.getInitialArray(), this.getInitialString(), this.toString(this.initialArray, true) };
		return result;
	}

	public int getNextState(int initialState, String readChar) throws IllegalArgumentException {
		int readCharIndex = (int) (this.validateTransition(initialState, readChar)[2]);
		return this.nextState[initialState][readCharIndex];
	}

	public int[][] getNextState() {
		int n = this.getNumStates(), s = this.getInputAlphabetSize();
		int[][] result = new int[n][s];
		for (int i = 0; i < n; i++) {
			System.arraycopy(this.nextState[i], 0, result[i], 0, s);
		}
		return result;
	}

	public boolean getDefined(int initialState, String readChar) throws IllegalArgumentException {
		int readCharIndex = (int) (this.validateTransition(initialState, readChar)[2]);
		return this.defined[initialState][readCharIndex];
	}

	public boolean[][] getDefined() {
		int n = this.getNumStates(), s = this.getInputAlphabetSize();
		boolean[][] result = new boolean[n][s];
		for (int i = 0; i < n; i++) {
			System.arraycopy(this.defined[i], 0, result[i], 0, s);
		}
		return result;
	}

	public int getTotalNumTransitions() {
		return this.totalNumTransitions;
	}

	public int getNumDefinedTransitions() {
		return this.numDefinedTransitions;
	}

	public int getStateNumDefined(int initialState) throws IllegalArgumentException {
		return this.stateNumDefined[this.validateState(initialState)];
	}

	public int[] getStateNumDefined() {
		int[] result = new int[this.getNumStates()];
		System.arraycopy(this.stateNumDefined, 0, result, 0, result.length);
		return result;
	}

	private String getTransition(int initialState, int readCharIndex, boolean format) {
		if (format) {
			return ("delta(" + initialState + ',' + this.inputAlphabet[readCharIndex] + ") = "
					+ this.nextState[initialState][readCharIndex]);
		}
		return (initialState + ' ' + this.inputAlphabet[readCharIndex] + ' '
				+ this.nextState[initialState][readCharIndex]);
	}

	public String getTransition(int initialState, String readChar, boolean format, boolean print)
			throws IllegalArgumentException {
		int readCharIndex = (int) (this.validateTransition(initialState, readChar)[2]);
		String transition = this.getTransition(initialState, readCharIndex, format);
		System.out.print(print ? (transition + '\n') : "");
		return transition;
	}

	public String getTransition(int initialState, String readChar, boolean format) throws IllegalArgumentException {
		return this.getTransition(initialState, readChar, format, false);
	}

	public String getTransition(int initialState, String readChar) throws IllegalArgumentException {
		return this.getTransition(initialState, readChar, false);
	}

	public String printTransition(int initialState, String readChar, boolean format) throws IllegalArgumentException {
		return this.getTransition(initialState, readChar, format, true);
	}

	public String printTransition(int initialState, String readChar) throws IllegalArgumentException {
		return this.printTransition(initialState, readChar, false);
	}

	public String[] getTransitions(int initialState, boolean format, boolean print) throws IllegalArgumentException {
		this.validateState(initialState);
		String[] result = new String[this.getInputAlphabetSize()];
		for (int i = 0; i < result.length; i++) {
			result[i] = this.getTransition(initialState, i, format);
			System.out.print(print ? (result[i] + '\n') : "");
		}
		return result;
	}

	public String[] getTransitions(int initialState, boolean format) throws IllegalArgumentException {
		return this.getTransitions(initialState, format, false);
	}

	public String[] getTransitions(int initialState) throws IllegalArgumentException {
		return this.getTransitions(initialState, false);
	}

	public String[] printTransitions(int initialState, boolean format) throws IllegalArgumentException {
		return this.getTransitions(initialState, format, true);
	}

	public String[] printTransitions(int initialState) throws IllegalArgumentException {
		return this.printTransitions(initialState, false);
	}

	public String[] getTransitions(boolean format, boolean print) {
		String[] result = new String[this.getTotalNumTransitions()];
		int index = 0;
		for (int i = 0; i < this.getNumStates(); i++) {
			for (int j = 0; j < this.getInputAlphabetSize(); j++) {
				result[index++] = this.getTransition(i, j, format);
				System.out.print(print ? (result[index - 1] + '\n') : "");
			}
		}
		return result;
	}

	public String[] getTransitions(boolean format) {
		return this.getTransitions(format, false);
	}

	public String[] getTransitions() {
		return this.getTransitions(false);
	}

	public String[] printTransitions(boolean format) {
		return this.getTransitions(format, true);
	}

	public String[] printTransitions() {
		return this.printTransitions(false);
	}

	public String getDefinedTransition(int initialState, String readChar, boolean format, boolean print)
			throws IllegalArgumentException {
		int readCharIndex = (int) (this.validateTransition(initialState, readChar)[2]);
		String transition = (this.defined[initialState][readCharIndex]
				? this.getTransition(initialState, readCharIndex, format)
				: null);
		System.out.print(print ? (transition + '\n') : "");
		return transition;
	}

	public String getDefinedTransition(int initialState, String readChar, boolean format)
			throws IllegalArgumentException {
		return this.getDefinedTransition(initialState, readChar, format, false);
	}

	public String getDefinedTransition(int initialState, String readChar) throws IllegalArgumentException {
		return this.getDefinedTransition(initialState, readChar, false);
	}

	public String printDefinedTransition(int initialState, String readChar, boolean format)
			throws IllegalArgumentException {
		return this.getDefinedTransition(initialState, readChar, format, true);
	}

	public String printDefinedTransition(int initialState, String readChar) throws IllegalArgumentException {
		return this.printDefinedTransition(initialState, readChar, false);
	}

	public String[] getDefinedTransitions(int initialState, boolean format, boolean print)
			throws IllegalArgumentException {
		this.validateState(initialState);
		int length = 0, s = this.getInputAlphabetSize();
		String transition;
		String[] temp = new String[s];
		for (int i = 0; i < s; i++) {
			transition = null;
			if (this.defined[initialState][i]) {
				transition = this.getTransition(initialState, i, format);
				length++;
			}
			temp[i] = transition;
		}

		String[] result = new String[length];
		for (int i = 0, index = 0; index < length; i++) {
			if ((transition = temp[i]) != null) {
				result[index++] = transition;
				System.out.print(print ? (transition + '\n') : "");
			}
		}
		return result;
	}

	public String[] getDefinedTransitions(int initialState, boolean format) throws IllegalArgumentException {
		return this.getDefinedTransitions(initialState, format, false);
	}

	public String[] getDefinedTransitions(int initialState) throws IllegalArgumentException {
		return this.getDefinedTransitions(initialState, false);
	}

	public String[] printDefinedTransitions(int initialState, boolean format) throws IllegalArgumentException {
		return this.getDefinedTransitions(initialState, format, true);
	}

	public String[] printDefinedTransitions(int initialState) throws IllegalArgumentException {
		return this.printDefinedTransitions(initialState, false);
	}

	public String[] getDefinedTransitions(boolean format, boolean print) {
		int index = 0, numDef = this.getNumDefinedTransitions();
		String[] result = new String[numDef];
		for (int i = 0; i < this.getNumStates() && index < numDef; i++) {
			for (int j = 0; j < this.getInputAlphabetSize() && index < numDef; j++) {
				if (this.defined[i][j]) {
					result[index++] = this.getTransition(i, j, format);
					System.out.print(print ? (result[index - 1] + '\n') : "");
				}
			}
		}
		return result;
	}

	public String[] getDefinedTransitions(boolean format) {
		return this.getDefinedTransitions(format, false);
	}

	public String[] getDefinedTransitions() {
		return this.getDefinedTransitions(false);
	}

	public String[] printDefinedTransitions(boolean format) {
		return this.getDefinedTransitions(format, true);
	}

	public String[] printDefinedTransitions() {
		return this.printDefinedTransitions(false);
	}

	public String getDefaultTransition(int initialState, String readChar, boolean format, boolean print)
			throws IllegalArgumentException {
		this.validateTransition(initialState, readChar);
		String transition = initialState + ' ' + readChar + ' ' + initialState;
		if (format) {
			transition = "delta(" + initialState + ',' + readChar + ") = " + initialState;
		}
		System.out.print(print ? (transition + '\n') : "");
		return transition;
	}

	public String getDefaultTransition(int initialState, String readChar, boolean format)
			throws IllegalArgumentException {
		return this.getDefaultTransition(initialState, readChar, format, false);
	}

	public String getDefaultTransition(int initialState, String readChar) throws IllegalArgumentException {
		return this.getDefaultTransition(initialState, readChar, false);
	}

	public String printDefaultTransition(int initialState, String readChar, boolean format)
			throws IllegalArgumentException {
		return this.getDefaultTransition(initialState, readChar, format, true);
	}

	public String printDefaultTransition(int initialState, String readChar) throws IllegalArgumentException {
		return this.printDefaultTransition(initialState, readChar, false);
	}

	public boolean getRun() {
		return this.run;
	}

	private boolean resetRun() {
		return (this.run = (this.getNumDefinedTransitions() > 0) && (this.getNumAcceptingStates() > 0)
				&& (this.getNumAcceptingStates() < this.getNumStates()));
	}

	public static boolean isDefault(String s) {
		return DFA.DEFAULT.equals(DFA.lower(s));
	}

	public int getMaxStringCount() {
		return this.maxStringCount;
	}

	public static boolean isValidMaxStringCount(int maxStringCount) {
		return (maxStringCount >= 0);
	}

	public int validateMaxStringCount(int maxStringCount) throws IllegalArgumentException {
		if (!DFA.isValidMaxStringCount(maxStringCount)) {
			this.cause = "Given max string count(" + maxStringCount + ") is negative.";
			this.illegalArg();
		}
		return maxStringCount;
	}

	public int setMaxStringCount(int maxStringCount) throws IllegalArgumentException {
		this.validateMaxStringCount(maxStringCount);
		this.strChange = this.strChange || this.getMaxStringCount() != maxStringCount;
		this.count = (this.maxStringCount = maxStringCount) > 1;
		return this.validateStringsCount(this.getMinLength(), this.getMaxLength());
	}

	private int validateStringsCount(int minLength, int maxLength) throws IllegalArgumentException {
		if (this.getMaxStringCount() > DFA.MAX_STRINGS_COUNT) {
			int max = Math.max(minLength, maxLength), start = this.isConstructing ? max : this.getInitialLength();
			int s = this.getInputAlphabetSize(), estimateStringCount;

			// in general estimateStringCount can be calculated from
			// (s^(max + 1) - s^start) / (s - 1)
			if (this.isConstructing) {
				// start == max and as such the expression simplifies to just
				// estimateStringCount = s^start by factoring and canceling out
				// s - 1 from numerator and denominator
				estimateStringCount = ((int) Math.pow(s, start));
			} else {
				int high = 1, low = 1;
				for (int i = 0; i < max + 1; i++) {
					high *= s;
					low *= i < start ? s : 1;
				}
				// high = s^(max + 1) and low = s^start
				estimateStringCount = (high - low) / (s - 1);
			}

			if (estimateStringCount > DFA.MAX_STRINGS_COUNT) {
				this.cause = "There is approximately " + estimateStringCount
						+ " strings to test which is more than the maximum(" + DFA.MAX_STRINGS_COUNT + ").";
				this.illegalArg();
			}
		}
		return this.getMaxStringCount();
	}

	public int getActualStringCount() {
		return this.actualStringCount;
	}

	public int getAcceptCount() {
		return this.acceptCount;
	}

	public int getRejectCount() {
		return this.rejectCount;
	}

	public HashMap<ArrayList<Integer>, String> getResults() {
		return new HashMap<ArrayList<Integer>, String>(this.results);
	}

	public int getMinLength() {
		return this.minLength;
	}

	// even if it returns true, minLength isn't necessarily valid since
	// initialLength hasn't been taken into account
	public static boolean isValidMinLength(int minLength) {
		return (minLength >= 0);
	}

	public int validateMinLength(int minLength) throws IllegalArgumentException {
		if (!DFA.isValidMinLength(minLength)) {
			this.cause = "Given min length(" + minLength + ") is negative.";
			this.illegalArg();
		}
		return minLength;
	}

	public int setMinLength(int minLength) throws IllegalArgumentException {
		this.validateMinLength(minLength);
		if (!this.isConstructing) {
			if (minLength > this.getInitialLength()) {
				this.cause = "Given min length(" + minLength + ") is greater than the initial string length("
						+ this.getInitialLength() + ").";
				this.illegalArg();
			} else if (this.checkStringsCount) {
				this.validateStringsCount(minLength, this.getMaxLength());
			}
		}
		this.strChange = this.strChange || (this.getMinLength() != minLength && this.getMaxStringCount() != 0);
		return (this.minLength = minLength);
	}

	public String getMinString(boolean format) {
		if (this.getMinLength() == 0) {
			return (format ? "The empty string" : "");
		}

		StringBuilder result = new StringBuilder("");
		String minChar = this.inputAlphabet[0];
		if (format) {
			result.append('"' + minChar);
			for (int i = 1; i < this.getMinLength(); i++) {
				result.append(' ' + minChar);
			}
			result.append('"');
		} else {
			for (int i = 0; i < this.getMinLength(); i++) {
				result.append(minChar);
			}
		}
		return result.toString();
	}

	public String getMinString() {
		return this.getMinString(false);
	}

	public ArrayList<Integer> getMinArray() {
		int minLength = this.getMinLength();
		ArrayList<Integer> result = new ArrayList<Integer>(minLength);
		for (int i = 0; i < minLength; i++) {
			result.add(0);
		}
		return result;
	}

	public int getMaxLength() {
		return this.maxLength;
	}

	// even if it returns true, maxLength isn't necessarily valid since
	// initialLength hasn't been taken into account
	public static boolean isValidMaxLength(int maxLength) {
		return (maxLength >= 0);
	}

	public int validateMaxLength(int maxLength) throws IllegalArgumentException {
		if (!DFA.isValidMaxLength(maxLength)) {
			this.cause = "Given max length(" + maxLength + ") is negative.";
			this.illegalArg();
		}
		return maxLength;
	}

	public int setMaxLength(int maxLength) throws IllegalArgumentException {
		this.validateMaxLength(maxLength);
		if (!this.isConstructing) {
			if (maxLength < this.getInitialLength()) {
				this.cause = "Given max length(" + maxLength + ") is less than the initial string length("
						+ this.getInitialLength() + ").";
				this.illegalArg();
			} else if (this.checkStringsCount) {
				this.validateStringsCount(this.getMinLength(), maxLength);
			}
		}
		this.strChange = this.strChange || (this.getMaxLength() != maxLength && this.getMaxStringCount() != 0);
		return (this.maxLength = maxLength);
	}

	public String getMaxString(boolean format) {
		if (this.getMaxLength() == 0) {
			return (format ? "The empty string" : "");
		}

		StringBuilder result = new StringBuilder("");
		String maxChar = this.inputAlphabet[this.getMaxInputIndex()];
		if (format) {
			result.append('"' + maxChar);
			for (int i = 1; i < this.getMaxLength(); i++) {
				result.append(' ' + maxChar);
			}
			result.append('"');
		} else {
			for (int i = 0; i < this.getMaxLength(); i++) {
				result.append(maxChar);
			}
		}
		return result.toString();
	}

	public String getMaxString() {
		return this.getMaxString(false);
	}

	public ArrayList<Integer> getMaxArray() {
		int maxLength = this.getMaxLength(), index = this.getMaxInputIndex();
		ArrayList<Integer> result = new ArrayList<Integer>(maxLength);
		for (int i = 0; i < maxLength; i++) {
			result.add(index);
		}
		return result;
	}

	public boolean inLengthRange(int length) {
		return (length >= this.getMinLength() && length <= this.getMaxLength());
	}

	public String getLengthRange() {
		return ('[' + this.getMinLength() + ", " + this.getMaxLength() + ']');
	}

	private String setLengthRange(int minLength, int maxLength, boolean checkStringsCount)
			throws IllegalArgumentException {
		// save field values in case of restoring
		int savedMin = this.getMinLength(), savedMax = this.getMaxLength();
		boolean savedCheckStringsCount = this.checkStringsCount, savedStrChange = this.strChange;
		try {
			this.checkStringsCount = false;
			this.setMinLength(Math.min(minLength, maxLength));
			this.setMaxLength(Math.max(minLength, maxLength));
			if (checkStringsCount) {
				this.validateStringsCount(minLength, maxLength);
			}
			this.checkStringsCount = savedCheckStringsCount;
			return this.getLengthRange();
		} catch (IllegalArgumentException ex) {
			if (!this.isConstructing) {
				this.minLength = savedMin;
				this.maxLength = savedMax;
				this.checkStringsCount = savedCheckStringsCount;
				this.strChange = savedStrChange;
			}
			this.illegalArg();
			return null;
		}
	}

	public String setLengthRange(int minLength, int maxLength) throws IllegalArgumentException {
		return this.setLengthRange(minLength, maxLength, true);
	}

	public Object[] setRangeString(int minLength, int maxLength, String initialString) throws IllegalArgumentException {
		// save field values in case of restoring
		boolean savedIsConstructing = this.isConstructing, savedStrChange = this.strChange;
		int savedMin = this.getMinLength(), savedMax = this.getMaxLength();
		try {
			this.isConstructing = true;
			this.setLengthRange(minLength, maxLength, false);
			this.isConstructing = savedIsConstructing;
		} catch (IllegalArgumentException ex) {
			this.isConstructing = savedIsConstructing;
			this.illegalArg();
		}

		Object[] result = null;
		ArrayList<Integer> a = null;
		try {
			// check if testString is defined over input alphabet
			a = this.validateTestString(initialString);
		} catch (IllegalArgumentException ex) {
			// since it isn't defined, check if isDefault
			if (this.isConstructing && DFA.isDefault(initialString)) {
				result = this.setInitialArray(this.getMinArray(), false);
			} else {
				if (!this.isConstructing) {
					this.minLength = savedMin;
					this.maxLength = savedMax;
					this.strChange = savedStrChange;
				}
				this.illegalArg();
			}
		}
		try {
			if (a != null) {
				// since it is defined, store it in the class variable
				result = this.setInitialArray(a, false);
			}
			this.validateStringsCount(this.getMinLength(), this.getMaxLength());
		} catch (IllegalArgumentException ex) {
			if (!this.isConstructing) {
				this.minLength = savedMin;
				this.maxLength = savedMax;
				this.strChange = savedStrChange;
			}
			this.illegalArg();
		}
		return result;
	}

	public Object[] setRangeArray(int minLength, int maxLength, ArrayList<Integer> initialArray)
			throws IllegalArgumentException {
		// save field values in case of restoring
		boolean savedIsConstructing = this.isConstructing, savedStrChange = this.strChange;
		int savedMin = this.getMinLength(), savedMax = this.getMaxLength();
		try {
			this.isConstructing = true;
			this.setLengthRange(minLength, maxLength, false);
			this.isConstructing = savedIsConstructing;
		} catch (IllegalArgumentException ex) {
			this.isConstructing = savedIsConstructing;
			this.illegalArg();
		}

		Object[] result = null;
		String s = null;
		try {
			// check if testString is defined over input alphabet
			s = this.validateTestString(initialArray);
		} catch (IllegalArgumentException ex) {
			if (this.isConstructing) {
				result = this.setInitialArray(this.getMinArray(), false);
			} else {
				if (!this.isConstructing) {
					this.minLength = savedMin;
					this.maxLength = savedMax;
					this.strChange = savedStrChange;
				}
				this.illegalArg();
			}
		}
		try {
			if (s != null) {
				// since it is defined, store it in the class variable
				result = this.setInitialArray(initialArray, false);
			}
			this.validateStringsCount(this.getMinLength(), this.getMaxLength());
		} catch (IllegalArgumentException ex) {
			if (!this.isConstructing) {
				this.minLength = savedMin;
				this.maxLength = savedMax;
				this.strChange = savedStrChange;
			}
			this.illegalArg();
		}
		return result;
	}

	public String getInitialString() {
		return this.initialString;
	}

	private Object[] setInitialString(String initialString, boolean validate) throws IllegalArgumentException {
		ArrayList<Integer> a = validate ? this.validateTestString(initialString) : this.toArray(initialString);
		if (initialString.equals(this.getInitialString())) {
			// impossible to happen when constructing since this.initialString is null
			return this.getInitialStringRepresentations();
		}

		if (!this.inLengthRange(a.size())) {
			if (this.count) {
				this.cause = "Given initial string(\"" + initialString + "\") has length " + a.size()
						+ " which isn't in the range of " + this.getLengthRange() + '.';
				this.illegalArg();
			} else {
				this.setLengthRange(0, a.size(), false);
			}
		}

		Object[] result = this.getInitialStringRepresentations();
		this.initialString = initialString;
		this.initialArray = a;
		this.strChange = true;
		return result;
	}

	public Object[] setInitialString(String initialString) throws IllegalArgumentException {
		return this.setInitialString(initialString, true);
	}

	public ArrayList<Integer> getInitialArray() {
		return new ArrayList<Integer>(this.initialArray);
	}

	private Object[] setInitialArray(ArrayList<Integer> initialArray, boolean validate)
			throws IllegalArgumentException {
		String s = null;
		if (validate) {
			s = this.validateTestString(initialArray);
		} else {
			this.isSimulating = true;
			s = this.toString(initialArray);
			this.isSimulating = false;
		}
		if (s.equals(this.getInitialString())) {
			// impossible to happen when constructing since this.initialString is null
			return this.getInitialStringRepresentations();
		}

		if (!this.inLengthRange(initialArray.size())) {
			if (this.count) {
				this.cause = "Given initial array represents \"" + s + "\" which has length " + initialArray.size()
						+ " which isn't in the range of " + this.getLengthRange() + '.';
				this.illegalArg();
			} else {
				this.setLengthRange(0, initialArray.size(), false);
			}
		}

		Object[] result = this.getInitialStringRepresentations();
		this.initialString = s;
		this.initialArray = new ArrayList<Integer>(initialArray);
		this.strChange = true;
		return result;
	}

	public Object[] setInitialArray(ArrayList<Integer> initialArray) throws IllegalArgumentException {
		return this.setInitialArray(initialArray, true);
	}

	public int getInitialLength() {
		return this.initialArray.size();
	}

	public ArrayList<Integer> toArray(String s) {
		if (s == null) {
			return null;
		}

		ArrayList<Integer> a = new ArrayList<Integer>(s.length());
		if (s.isEmpty()) {
			return a;
		}

		String check = s;
		int i = 1, index;
		while (i <= check.length()) {
			if ((index = this.inputCharIndexOf(check.substring(0, i))) == -1) {
				i++;
			} else {
				a.add(index);
				if (i < check.length()) {
					check = check.substring(i);
					i = 1;
				} else {
					return a;
				}
			}
		}
		return null;
	}

	public String toString(ArrayList<Integer> testString, boolean format) throws IllegalArgumentException {
		if (!this.isSimulating && !this.isValidTestString(testString)) {
			return null;
		}

		if (testString.isEmpty()) {
			return (format ? "The empty string" : "");
		}

		StringBuilder output = new StringBuilder("");
		if (format) {
			output.append('"' + this.inputAlphabet[testString.get(0)]);
			for (int i = 1; i < testString.size(); i++) {
				output.append(' ' + this.inputAlphabet[testString.get(i)]);
			}
			output.append('"');
		} else {
			for (int i = 0; i < testString.size(); i++) {
				output.append(this.inputAlphabet[testString.get(i)]);
			}
		}
		return output.toString();
	}

	public String toString(ArrayList<Integer> testString) throws IllegalArgumentException {
		return this.toString(testString, false);
	}

	public boolean isValidTestString(String testString) {
		return (this.toArray(testString) != null);
	}

	public boolean isValidTestString(ArrayList<Integer> testString) {
		if (testString == null) {
			return false;
		}

		for (int i : testString) {
			if (!this.isValidInputCharIndex(i)) {
				return false;
			}
		}

		return true;
	}

	public ArrayList<Integer> validateTestString(String testString) throws IllegalArgumentException {
		ArrayList<Integer> a = this.toArray(testString);
		if (a == null) {
			this.cause = "Given " + (this.isConstructing ? "initial" : "test") + " string";
			this.cause += "(\"" + testString + "\") isn't defined over the given input alphabet.";
			this.illegalArg();
		}
		return a;
	}

	public String validateTestString(ArrayList<Integer> testString) throws IllegalArgumentException {
		String s = this.toString(testString);
		if (s == null) {
			this.cause = "Given " + (this.isConstructing ? "initial" : "test") + " array";
			this.cause += "represents a string that isn't defined over the given input alphabet.";
			this.illegalArg();
		}
		return s;
	}

	public boolean getIncludeComments() {
		return this.includeComments;
	}

	public boolean setIncludeComments(boolean includeComments) {
		this.strChange = this.strChange || this.getIncludeComments() != includeComments;
		return (this.includeComments = includeComments);
	}

	public String getComments() {
		if (!this.comChange) {
			return this.savedCom;
		}
		this.comChange = false;
		return (this.savedCom = this.comments.toString());
	}

	public String offerComments(String comments) {
		if (this.savedCom != null) {
			if (this.savedCom.equals(comments)) {
				return this.setComments(comments);
			} else if (this.getComments().equals(comments)) {
				return comments;
			}
		}
		return this.setComments(comments);
	}

	public String offerComments(CharSequence comments) {
		return this.offerComments(comments.toString());
	}

	public String offerComments() {
		return this.offerComments("");
	}

	public String setComments(String comments) {
		String temp = comments != null ? comments : "";
		this.comments = new StringBuilder(temp);
		this.strChange = this.strChange || this.getIncludeComments();
		this.comChange = false;
		return (this.savedCom = temp);
	}

	public String setComments(CharSequence comments) {
		return this.setComments(comments.toString());
	}

	public String setComments() {
		return this.setComments("");
	}

	public void appendComments(CharSequence comments) {
		if (comments != null && comments.length() != 0) {
			this.comments.append(comments);
			this.comChange = true;
			this.strChange = this.strChange || this.getIncludeComments();
		}
	}

	public String getCause() {
		return this.cause;
	}

	public static String getStaticCause() {
		return DFA.staticCause;
	}

	public String getTime() {
		return this.time;
	}

	public HashMap<String, String> getMachines() {
		return new HashMap<String, String>(this.machines);
	}

	public static int getMachineCount() {
		return DFA.machineCount;
	}

	public boolean getOverwrote() {
		return this.overwrote;
	}

	public DFA(int numStates, int inputAlphabetSize, String[] inputAlphabet, int numAcceptingStates, int[] accepting,
			int numTransitions, String[] transitions, int maxStringCount, int minLength, int maxLength,
			String initialString, boolean includeComments, String comments) throws IllegalArgumentException {
		this.isConstructing = true;
		this.setNumStates(numStates);
		this.setAlphabet(inputAlphabetSize, inputAlphabet);
		this.setAccepting(numAcceptingStates, accepting);
		this.putTransitions(numTransitions, transitions);
		this.setMaxStringCount(maxStringCount);
		this.setRangeString(minLength, maxLength, initialString);
		this.setIncludeComments(includeComments);
		this.offerComments(comments);
		this.isConstructing = false;
		this.cause = DFA.staticCause = null;
		DFA.machineCount++;
	}

	public DFA(int numStates, int inputAlphabetSize, String[] inputAlphabet, int numAcceptingStates, int[] accepting,
			int numTransitions, String[] transitions, int maxStringCount, int minLength, int maxLength,
			String initialString, boolean includeComments) throws IllegalArgumentException {
		this(numStates, inputAlphabetSize, inputAlphabet, numAcceptingStates, accepting, numTransitions, transitions,
				maxStringCount, minLength, maxLength, initialString, includeComments, null);
	}

	public DFA(int numStates, int inputAlphabetSize, String[] inputAlphabet, int numAcceptingStates, int[] accepting,
			int numTransitions, String[] transitions, int maxStringCount, int minLength, int maxLength,
			String initialString) throws IllegalArgumentException {
		this(numStates, inputAlphabetSize, inputAlphabet, numAcceptingStates, accepting, numTransitions, transitions,
				maxStringCount, minLength, maxLength, initialString, DFA.DEFAULT_INCLUDE_COMMENTS);
	}

	public DFA(int numStates, int inputAlphabetSize, String[] inputAlphabet, int numAcceptingStates, int[] accepting,
			int numTransitions, String[] transitions, int maxStringCount, int minLength, int maxLength)
			throws IllegalArgumentException {
		this(numStates, inputAlphabetSize, inputAlphabet, numAcceptingStates, accepting, numTransitions, transitions,
				maxStringCount, minLength, maxLength, DFA.DEFAULT_INITIAL_STRING);
	}

	public DFA(int numStates, int inputAlphabetSize, String[] inputAlphabet, int numAcceptingStates, int[] accepting,
			int numTransitions, String[] transitions, int maxStringCount, int maxLength)
			throws IllegalArgumentException {
		this(numStates, inputAlphabetSize, inputAlphabet, numAcceptingStates, accepting, numTransitions, transitions,
				maxStringCount, DFA.DEFAULT_MIN_LENGTH, maxLength);
	}

	public DFA(int numStates, int inputAlphabetSize, String[] inputAlphabet, int numAcceptingStates, int[] accepting,
			int numTransitions, String[] transitions, int maxStringCount) throws IllegalArgumentException {
		this(numStates, inputAlphabetSize, inputAlphabet, numAcceptingStates, accepting, numTransitions, transitions,
				maxStringCount, DFA.DEFAULT_MAX_LENGTH);
	}

	public DFA(int numStates, int inputAlphabetSize, String[] inputAlphabet, int numAcceptingStates, int[] accepting,
			int numTransitions, String[] transitions) throws IllegalArgumentException {
		this(numStates, inputAlphabetSize, inputAlphabet, numAcceptingStates, accepting, numTransitions, transitions,
				DFA.DEFAULT_MAX_STRING_COUNT);
	}

	public DFA(int numStates, int inputAlphabetSize, String[] inputAlphabet, int numAcceptingStates, int[] accepting)
			throws IllegalArgumentException {
		this(numStates, inputAlphabetSize, inputAlphabet, numAcceptingStates, accepting, 0, new String[0]);
	}

	public DFA(int numStates, int inputAlphabetSize, String[] inputAlphabet) throws IllegalArgumentException {
		this(numStates, inputAlphabetSize, inputAlphabet, 0, new int[0]);
	}

	public DFA(int inputAlphabetSize, String[] inputAlphabet) throws IllegalArgumentException {
		this(DFA.MIN_NUM_STATES, inputAlphabetSize, inputAlphabet);
	}

	// copy constructor
	public DFA(DFA other) throws NullPointerException {
		this(other.getNumStates(), other.getInputAlphabetSize(), other.getInputAlphabet(),
				other.getNumAcceptingStates(), other.getAcceptingStates(), other.getNumDefinedTransitions(),
				other.getDefinedTransitions(), other.getMaxStringCount(), other.getMinLength(), other.getMaxLength(),
				other.getInitialString(), other.getIncludeComments(), other.getComments());
	}

	public DFA getCopy() {
		return new DFA(this);
	}

	// by creating a copy from calling the toString method,
	// the value of toString is saved for this instance as well
	public DFA getStringCopy() {
		return new DFA(this.toString());
	}

	// creates a deterministic finite automata by reading it (in YUFAFF) from in
	@SuppressWarnings("null")
	public DFA(Scanner in) throws IllegalArgumentException {
		this.isScanning = this.isConstructing = true;

		if (in == null) {
			DFA.staticCause = "Given scanner is null.";
			DFA.illegalArg(DFA.getStaticCause());
		}

		try {
			if (!in.hasNextLine()) {
				DFA.staticCause = "Given machine description didn't have a first line.";
				DFA.illegalArg(DFA.getStaticCause());
			}
			// process first line
			String line = in.nextLine();
			this.lineNumber++;
			String[] s = line.split(DFA.DELIMITER_STRING);
			if (s.length != DFA.LINE_1_NUM_ENTRIES || DFA.countDelimiters(line) != s.length - 1) {
				DFA.staticCause = "Given first line(" + line + ") isn't valid.";
				DFA.illegalArg(DFA.getStaticCause());
			}

			int numStates = DFA.MIN_NUM_STATES;
			try {
				numStates = Integer.parseInt(s[0]);
			} catch (NumberFormatException ex) {
				DFA.staticCause = "Given number of states(" + s[0] + ") isn't a valid integer.";
				DFA.illegalArg(DFA.getStaticCause());
			}
			try {
				this.setNumStates(numStates);
			} catch (IllegalArgumentException ex) {
				DFA.staticCause = this.getCause();
				this.illegalArg();
			}

			int inputAlphabetSize = DFA.MIN_INPUT_ALPHABET_SIZE;
			try {
				inputAlphabetSize = Integer.parseInt(s[1]);
			} catch (NumberFormatException ex) {
				DFA.staticCause = "Given input alphabet size(" + s[1] + ") isn't a valid integer.";
				DFA.illegalArg(DFA.getStaticCause());
			}

			int numAcceptingStates = 0;
			try {
				if ((numAcceptingStates = Integer.parseInt(s[2])) < 0) {
					DFA.staticCause = "Given number of accepting states(" + numAcceptingStates + ") is negative.";
					DFA.illegalArg(DFA.getStaticCause());
				}
			} catch (NumberFormatException ex) {
				DFA.staticCause = "Given number of accepting states(" + s[2] + ") isn't a valid integer.";
				DFA.illegalArg(DFA.getStaticCause());
			}

			int numTransitions = 0;
			try {
				if ((numTransitions = Integer.parseInt(s[3])) < 0) {
					DFA.staticCause = "Given number of transitions(" + numTransitions + ") is negative.";
					DFA.illegalArg(DFA.getStaticCause());
				}
			} catch (NumberFormatException ex) {
				DFA.staticCause = "Given number of transitions(" + s[3] + ") isn't a valid integer.";
				DFA.illegalArg(DFA.getStaticCause());
			}

			if (!in.hasNextLine()) {
				DFA.staticCause = "Given machine description didn't have a second line.";
				DFA.illegalArg(DFA.getStaticCause());
			}
			// process second line
			line = in.nextLine();
			this.lineNumber++;
			s = line.split(DFA.DELIMITER_STRING);
			if (s.length != inputAlphabetSize || DFA.countDelimiters(line) != s.length - 1) {
				DFA.staticCause = "Given second line(" + line + ") isn't valid.";
				DFA.illegalArg(DFA.getStaticCause());
			}
			try {
				this.setAlphabet(inputAlphabetSize, s);
			} catch (IllegalArgumentException ex) {
				DFA.staticCause = this.getCause();
				this.illegalArg();
			}

			if (!in.hasNextLine()) {
				DFA.staticCause = "Given machine description didn't have a third line.";
				DFA.illegalArg(DFA.getStaticCause());
			}
			// process third line
			line = in.nextLine();
			this.lineNumber++;
			int[] accepting = new int[numAcceptingStates];
			if (numAcceptingStates == 0) {
				if (!line.isEmpty()) {
					DFA.staticCause = "Given third line(" + line + ") isn't empty.";
					DFA.illegalArg(DFA.getStaticCause());
				}
			} else {
				s = line.split(DFA.DELIMITER_STRING);
				if (s.length != numAcceptingStates || DFA.countDelimiters(line) != s.length - 1) {
					DFA.staticCause = "Given third line(" + line + ") isn't valid.";
					DFA.illegalArg(DFA.getStaticCause());
				}

				for (int i = 0; i < numAcceptingStates; i++) {
					try {
						accepting[i] = Integer.parseInt(s[i]);
					} catch (NumberFormatException ex) {
						DFA.staticCause = "Given " + (i + 1) + "th accept state index(" + s[i]
								+ ") isn't a valid integer.";
						DFA.illegalArg(DFA.getStaticCause());
					}
				}
			}
			try {
				this.setAccepting(numAcceptingStates, accepting);
			} catch (IllegalArgumentException ex) {
				DFA.staticCause = this.getCause();
				this.illegalArg();
			}

			// process transition lines
			String[] transitions = new String[numTransitions];
			for (int i = 0; i < numTransitions; i++) {
				if (!in.hasNextLine()) {
					DFA.staticCause = "Given machine description didn't have line " + (i + 4) + '.';
					DFA.illegalArg(DFA.getStaticCause());
				}
				transitions[i] = in.nextLine();
			}
			try {
				this.putTransitions(numTransitions, transitions);
			} catch (IllegalArgumentException ex) {
				DFA.staticCause = this.getCause();
				this.illegalArg();
			}

			int readMaxStringCount = DFA.DEFAULT_MAX_STRING_COUNT, readMinLength = DFA.DEFAULT_MIN_LENGTH,
					readMaxLength = DFA.DEFAULT_MAX_LENGTH;
			String readInitialString = DFA.DEFAULT_INITIAL_STRING;
			// process command line
			if (in.hasNextLine()) {
				line = in.nextLine();
				this.lineNumber++;
				if (!line.isEmpty()) {
					s = line.split(DFA.DELIMITER_STRING);
					if (s.length > DFA.COMMAND_LINE_MAX_NUM_ENTRIES || DFA.countDelimiters(line) != s.length - 1) {
						DFA.staticCause = "Given command line(" + line + ") isn't valid.";
						DFA.illegalArg(DFA.getStaticCause());
					}

					try {
						readMaxStringCount = Integer.parseInt(s[0]);
					} catch (NumberFormatException ex) {
						if (!DFA.isDefault(s[0])) {
							DFA.staticCause = "Given max string count(" + s[0] + ") isn't a valid integer.";
							DFA.illegalArg(DFA.getStaticCause());
						}
					}

					if (readMaxStringCount != 0) {
						if (s.length == 2) {
							try {
								readMaxLength = Integer.parseInt(s[1]);
							} catch (NumberFormatException ex) {
								if (!DFA.isDefault(s[1])) {
									DFA.staticCause = "Given max length(" + s[1] + ") isn't a valid integer.";
									DFA.illegalArg(DFA.getStaticCause());
								}
							}
						}

						if (s.length >= 3) {
							int first = DFA.DEFAULT_MIN_LENGTH;
							int second = DFA.DEFAULT_MAX_LENGTH;
							try {
								first = Integer.parseInt(s[1]);
							} catch (NumberFormatException ex) {
								if (!DFA.isDefault(s[1])) {
									DFA.staticCause = "Given first value for the string length bounds(" + s[1]
											+ ") isn't a valid integer.";
									DFA.illegalArg(DFA.getStaticCause());
								}
							}
							try {
								second = Integer.parseInt(s[2]);
							} catch (NumberFormatException ex) {
								if (!DFA.isDefault(s[2])) {
									DFA.staticCause = "Given second value for the string length bounds(" + s[2]
											+ ") isn't a valid integer.";
									DFA.illegalArg(DFA.getStaticCause());
								}
							}

							readMinLength = Math.min(first, second);
							readMaxLength = Math.max(first, second);
							for (int i = 0; i < readMinLength; i++) {
								readInitialString += this.inputAlphabet[0];
							}
						}

						readInitialString = s.length == 4 ? s[3] : readInitialString;
					}
				}
			}
			try {
				this.setMaxStringCount(readMaxStringCount);
				this.setRangeString(readMinLength, readMaxLength, readInitialString);
			} catch (IllegalArgumentException ex) {
				DFA.staticCause = this.getCause();
				this.illegalArg();
			}

			// process comments
			this.setIncludeComments(DFA.DEFAULT_INCLUDE_COMMENTS);
			StringBuilder comments = new StringBuilder("");
			while (in.hasNextLine()) {
				comments.append(in.nextLine() + '\n');
				this.lineNumber++;
			}
			in.close(); // close upon success
			// trim last extra '\n' from comments if it exists
			this.offerComments(comments.length() == 0 ? comments : comments.subSequence(0, comments.length() - 1));

			this.isScanning = this.isConstructing = false;
			this.cause = DFA.staticCause = null;
			DFA.machineCount++;
		} catch (IllegalArgumentException ex) {
			in.close(); // close upon failure to avoid resource leak
			ex.printStackTrace();
			throw new IllegalArgumentException(ex.getMessage());
		} catch (IllegalStateException ex) {
			// no need to close scanner since it's already closed
			ex.printStackTrace();
			DFA.staticCause = "Given scanner is closed.";
			DFA.illegalArg(DFA.getStaticCause());
		}
	}

	@SuppressWarnings("resource")
	public DFA(File f) throws IllegalArgumentException, NullPointerException, FileNotFoundException {
		this(new Scanner(f));
	}

	@SuppressWarnings("resource")
	public DFA(String s, boolean isPathName)
			throws IllegalArgumentException, NullPointerException, FileNotFoundException {
		this(isPathName ? new Scanner(new File(s)) : new Scanner(s));
	}

	@SuppressWarnings("resource")
	public DFA(CharSequence c) throws IllegalArgumentException, NullPointerException {
		this(new Scanner(c.toString()));
	}

	@SuppressWarnings("resource")
	public DFA(InputStream s) throws IllegalArgumentException, NullPointerException {
		this(new Scanner(s));
	}

	public DFA() throws IllegalArgumentException {
		this(System.in);
	}

	@SuppressWarnings("null")
	public String[] putTransitions(int numTransitions, String[] transitions, boolean[] replace)
			throws IllegalArgumentException {
		if (numTransitions < 0) {
			this.cause = "Given number of transitions(" + numTransitions + ") is negative.";
			this.illegalArg();
		} else if (transitions == null || transitions.length != numTransitions) {
			this.cause = "Given transitions array isn't valid.";
			this.illegalArg();
		} else if (replace == null || replace.length != numTransitions) {
			this.cause = "Given replacement array isn't valid.";
			this.illegalArg();
		}

		for (int i = 0; i < numTransitions; i++) {
			String line = transitions[i];
			// increment lineNumber regardless since it's a private variable with no accessor
			this.lineNumber++;
			if (line == null) {
				this.cause = "Given transitions array isn't valid since it contains null at index " + i + '.';
				this.illegalArg();
			}
			Object[] result = this.validateTransition(line);

			try {
				this.putTransition((int) result[0], (String) result[1], (int) result[2], replace[i]);
			} catch (IllegalArgumentException ex) {
				if (!this.isScanning) {
					this.cause = "Given " + (i + 1) + "th transition(" + line + ") isn't valid.";
				}
				this.illegalArg();
			}
		}
		return transitions;
	}

	public String[] putTransitions(int numTransitions, String[] transitions, boolean replace)
			throws IllegalArgumentException {
		if (numTransitions < 0) {
			this.cause = "Given number of transitions(" + numTransitions + ") is negative.";
			this.illegalArg();
		}
		boolean[] replacement = new boolean[numTransitions];
		if (replace) {
			Arrays.fill(replacement, true);
		}
		return this.putTransitions(numTransitions, transitions, replacement);
	}

	public String[] putTransitions(int numTransitions, String[] transitions) throws IllegalArgumentException {
		return this.putTransitions(numTransitions, transitions, false);
	}

	public String putTransition(int initialState, String readChar, int finalState, boolean replace)
			throws IllegalArgumentException {
		int readCharIndex = (int) (this.validateTransition(initialState, readChar, finalState)[3]);
		String transition = initialState + ' ' + readChar + ' ' + finalState;
		if (!replace && this.defined[initialState][readCharIndex]) {
			this.cause = "Given transition";
			if (this.isScanning) {
				this.cause += " on line " + this.lineNumber;
			}
			this.cause += '(' + transition + ") has the same initial state and input character"
					+ " as another transition defined before it.";
			this.illegalArg();
		}

		this.nextState[initialState][readCharIndex] = finalState;
		if (!this.defined[initialState][readCharIndex]) {
			this.defined[initialState][readCharIndex] = true;
			this.numDefinedTransitions++;
			this.stateNumDefined[initialState]++;
			this.resetRun();
		}
		this.strChange = true;
		return transition;
	}

	public String putTransition(int initialState, String readChar, int finalState) throws IllegalArgumentException {
		return this.putTransition(initialState, readChar, finalState, false);
	}

	public boolean isValidTransition(String transition) {
		try {
			Object[] result = this.validateTransition(transition);
			return this.isValidTransition((int) result[0], (String) result[1], (int) result[2]);
		} catch (IllegalArgumentException ex) {
			return false;
		}
	}

	public boolean isValidTransition(int initialState, String readChar, int finalState) {
		try { // if no exception is thrown then the result is necessarily true
			return (this.validateTransition(initialState, readChar, finalState) != null);
		} catch (IllegalArgumentException ex) {
			return false;
		}
	}

	public boolean isValidDefinedTransition(String transition) throws IllegalArgumentException {
		Object[] result = this.validateTransition(transition);
		return this.isValidDefinedTransition((int) result[0], (String) result[1], (int) result[2]);
	}

	public boolean isValidDefinedTransition(int initialState, String readChar, int finalState)
			throws IllegalArgumentException {
		int readCharIndex = (int) (this.validateTransition(initialState, readChar, finalState)[3]);
		return this.defined[initialState][readCharIndex];
	}

	@SuppressWarnings("null")
	public Object[] validateTransition(String transition) throws IllegalArgumentException {
		if (transition == null) {
			this.cause = "Given transition is null.";
			this.illegalArg();
		}

		String[] s = transition.split(DFA.DELIMITER_STRING);
		if (s.length != 3 || DFA.countDelimiters(transition) != s.length - 1) {
			this.cause = "Given transition(" + transition + ") isn't valid.";
			if (this.isScanning) {
				this.cause = "Line " + this.lineNumber + '(' + transition + ") isn't valid.";
			}
			this.illegalArg();
		}

		int initialState = 0;
		try {
			initialState = Integer.parseInt(s[0]);
		} catch (NumberFormatException ex) {
			this.cause = "Given initial state";
			if (this.isScanning) {
				this.cause += " on line " + this.lineNumber;
			}
			this.cause += '(' + s[0] + ") isn't a valid integer.";
			this.illegalArg();
		}

		int finalState = 0;
		try {
			finalState = Integer.parseInt(s[2]);
		} catch (NumberFormatException ex) {
			this.cause = "Given final state";
			if (this.isScanning) {
				this.cause += " on line " + this.lineNumber;
			}
			this.cause += '(' + s[2] + ") isn't a valid integer.";
			this.illegalArg();
		}

		Object[] result = { initialState, s[1], finalState };
		return result;
	}

	public Object[] validateTransition(int initialState, String readChar, int finalState)
			throws IllegalArgumentException {
		int readCharIndex = (int) (this.validateTransition(initialState, readChar)[2]);
		Object[] result = { initialState, readChar, this.validateState(finalState, false), readCharIndex };
		return result;
	}

	public Object[] validateTransition(int initialState, String readChar) throws IllegalArgumentException {
		Object[] result = { this.validateState(initialState), readChar, this.validateInputChar(readChar) };
		return result;
	}

	private String resetTransition(int initialState, int readCharIndex) {
		String transition = this.getTransition(initialState, readCharIndex, false);
		// set default value
		this.nextState[initialState][readCharIndex] = initialState;
		return transition;
	}

	private void finalizeReset(int initialState, int readCharIndex) {
		this.defined[initialState][readCharIndex] = false;
		this.numDefinedTransitions--;
		this.stateNumDefined[initialState]--;
		this.resetRun();
		this.strChange = true;
	}

	public String resetTransition(int initialState, String readChar) throws IllegalArgumentException {
		int readCharIndex = (int) (this.validateTransition(initialState, readChar)[2]);
		String transition = this.resetTransition(initialState, readCharIndex);
		if (this.defined[initialState][readCharIndex]) {
			this.finalizeReset(initialState, readCharIndex);
		}
		return transition;
	}

	public String[] resetTransitions(int initialState) throws IllegalArgumentException {
		this.validateState(initialState);
		String[] result = new String[this.getInputAlphabetSize()];
		for (int i = 0; i < result.length; i++) {
			result[i] = this.resetTransition(initialState, i);
			if (this.defined[initialState][i]) {
				this.finalizeReset(initialState, i);
			}
		}
		return result;
	}

	public String[] resetTransitions() {
		String[] result = new String[this.getTotalNumTransitions()];
		int index = 0;
		for (int i = 0; i < this.getNumStates(); i++) {
			this.stateNumDefined[i] = 0;
			for (int j = 0; j < this.getInputAlphabetSize(); j++) {
				result[index++] = this.resetTransition(i, j);
				this.defined[i][j] = false;
			}
		}
		if (this.getNumDefinedTransitions() != 0) {
			this.numDefinedTransitions = 0;
			this.resetRun();
			this.strChange = true;
		}
		return result;
	}

	public String resetDefinedTransition(int initialState, String readChar) throws IllegalArgumentException {
		int readCharIndex = (int) (this.validateTransition(initialState, readChar)[2]);
		String transition = null;
		if (this.defined[initialState][readCharIndex]) {
			transition = this.resetTransition(initialState, readCharIndex);
			this.finalizeReset(initialState, readCharIndex);
		}
		return transition;
	}

	public String[] resetDefinedTransitions(int initialState) throws IllegalArgumentException {
		this.validateState(initialState);
		int length = 0, s = this.getInputAlphabetSize();
		String transition;
		String[] temp = new String[s];
		for (int i = 0; i < s && this.stateNumDefined[initialState] != 0; i++) {
			transition = null;
			if (this.defined[initialState][i]) {
				transition = this.resetTransition(initialState, i);
				this.finalizeReset(initialState, i);
				length++;
			}
			temp[i] = transition;
		}

		String[] result = new String[length];
		for (int i = 0, index = 0; index < length; i++) {
			if ((transition = temp[i]) != null) {
				result[index++] = transition;
			}
		}
		return result;
	}

	public String[] resetDefinedTransitions() {
		String[] result = new String[this.getNumDefinedTransitions()];
		int index = 0;
		for (int i = 0; i < this.getNumStates() && this.getNumDefinedTransitions() != 0; i++) {
			for (int j = 0; j < this.getInputAlphabetSize() && this.getNumDefinedTransitions() != 0; j++) {
				if (this.defined[i][j]) {
					result[index++] = this.resetTransition(i, j);
					this.finalizeReset(i, j);
				}
			}
		}
		return result;
	}

	private void initializeTransitions() {
		int n = this.getNumStates(), s = this.getInputAlphabetSize();
		this.nextState = new int[n][s];
		this.defined = new boolean[n][s];
		this.numDefinedTransitions = 0;
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < s; j++) {
				this.nextState[i][j] = i; // set default value
			}
		}
		this.strChange = true;
	}

	@SuppressWarnings("null")
	public static int countDelimiters(String s) throws IllegalArgumentException {
		if (s == null) {
			DFA.staticCause = "Given string is null.";
			DFA.illegalArg(DFA.getStaticCause());
		}

		int count = 0;
		for (int i = 0; i < s.length(); i++) {
			count += s.charAt(i) == DFA.DELIMITER_CHAR ? 1 : 0;
		}
		return count;
	}

	public static String lower(String s) {
		if (s == null) {
			return null;
		}

		String lower = s.toLowerCase();
		if (s.length() <= 1) {
			return lower;
		} else if (s.substring(1).equals(lower.substring(1))) {
			return lower; // matches [A-Z][a-z]*
		} else if (s.equals(s.toUpperCase())) {
			return lower; // matches [A-Z]+
		}

		return null;
	}

	public static boolean isValidBoolean(String s) {
		try { // if no exception is thrown then the result is necessarily true
			return (DFA.parseBoolean(s) || true);
		} catch (IllegalArgumentException ex) {
			return false;
		}
	}

	public static boolean parseBoolean(String s) throws IllegalArgumentException {
		if (s == null) {
			DFA.staticCause = "Given string is null.";
			DFA.illegalArg(DFA.getStaticCause());
		}

		String check = DFA.lower(s);
		if (check != null) {
			if (check.equals(DFA.TRUE_1) || check.equals(DFA.TRUE_2)) {
				return true;
			} else if (check.equals(DFA.FALSE_1) || check.equals(DFA.FALSE_2)) {
				return false;
			}
		}

		DFA.staticCause = "Given string(" + s + ") doesn't represent valid a boolean.";
		DFA.illegalArg(DFA.getStaticCause());
		return false;
	}

	public String simulate(boolean print) {
		this.isSimulating = true;

		ArrayList<Integer> testString = this.getInitialArray();
		String message, value = "";

		if (print) {
			this.printMachine();
			if (this.getMaxStringCount() == 0) {
				System.out.println("\nTesting no strings!");
			} else {
				if (this.getMaxStringCount() == 1) {
					System.out.print("\nStarting to test ");
				} else {
					System.out.println(
							"\nStarting to test strings of length in the range of " + this.getLengthRange() + '.');
					System.out.print(
							"Testing the first " + DFA.comma(this.getMaxStringCount()) + " strings starting from ");
				}
				message = this.toString(testString, true).toLowerCase();
				System.out.println(message + '.' + (this.getMaxStringCount() != 1 ? '\n' : ""));
			}
		}

		this.acceptCount = this.rejectCount = 0;
		// maps testString to accept:stepCount
		this.results = new HashMap<ArrayList<Integer>, String>(this.getMaxStringCount());

		long beforeTime = System.nanoTime(), elapsedTime;
		int count = 0;
		while (testString.size() <= this.getMaxLength() && ++count <= this.getMaxStringCount()) {
			if (this.getRun()) {
				boolean accept = this.accept(testString);
				value = accept + ":" + testString.size();
				this.results.put(testString, value);

				if (print) {
					message = this.toString(testString, true) + " was ";
					message += accept ? "accepted in " : "rejected in ";
					System.out.println(
							message + DFA.comma(testString.size()) + (testString.size() == 1 ? " step." : " steps."));
				}
			} else if (this.getNumAcceptingStates() == 0) {
				this.incrementCount(false);
				value = "false:0";
				this.results.put(testString, value);

				if (print) {
					message = this.toString(testString, true);
					System.out.println(message + " was rejected in 0 steps!");
				}
			} else if (this.getNumAcceptingStates() == this.getNumStates()) {
				this.incrementCount(true);
				value = "true:0";
				this.results.put(testString, value);

				if (print) {
					message = this.toString(testString, true);
					System.out.println(message + " was accepted in 0 steps!");
				}
			} else { // this.getNumDefinedTransitions() == 0
				boolean accept = this.accepting[0];
				this.incrementCount(accept);
				value = accept + ":" + testString.size();
				this.results.put(testString, value);

				if (print) {
					message = this.toString(testString, true) + " was ";
					message += accept ? "accepted" : "rejected";
					System.out.println(message + " in 0 steps!");
				}
			}

			this.incrementTestString(testString);
		}
		elapsedTime = DFA.nano2Milli(System.nanoTime() - beforeTime);
		;
		this.time = DFA.formatTime(elapsedTime);

		this.actualStringCount = Math.min(this.getMaxStringCount(), count);

		if (print) {
			this.printSimulationInfo();
		}

		this.isSimulating = false;
		if (this.getActualStringCount() == 0) {
			return null;
		} else if (this.getActualStringCount() == 1) {
			return value;
		}
		return (this.getAcceptCount() + ":" + this.getRejectCount());
	}

	public String simulate() {
		return this.simulate(true);
	}

	private boolean accept(ArrayList<Integer> testString) {
		int initialState = 0;
		boolean accept = this.accept(testString, initialState);
		return this.incrementCount(accept);
	}

	private boolean incrementCount(boolean accept) {
		if (this.count) {
			if (accept) {
				this.acceptCount++;
			} else {
				this.rejectCount++;
			}
		}
		return accept;
	}

	// checks whether machine accepts the string described by testString
	public boolean accept(ArrayList<Integer> testString, int state) throws IllegalArgumentException {
		if (!this.isSimulating) {
			this.validateState(state);
			this.validateTestString(testString);
		}

		for (int i = 0; i < testString.size(); i++) {
			state = this.nextState[state][testString.get(i)];
		}
		return this.accepting[state];
	}

	public ArrayList<Integer> incrementTestString(ArrayList<Integer> testString) throws IllegalArgumentException {
		if (!this.isSimulating) {
			this.validateTestString(testString);
		}

		int pos = testString.size() - 1, index = this.getMaxInputIndex();
		while (pos >= 0 && testString.get(pos) == index) {
			testString.set(pos--, 0);
		}
		if (pos != -1) {
			testString.set(pos, testString.get(pos) + 1);
		} else {
			testString.add(0); // only when testString is the max string of its length
		}
		return testString;
	}

	public boolean isMinTestString(ArrayList<Integer> testString) throws IllegalArgumentException {
		if (!this.isSimulating) {
			this.validateTestString(testString);
		}

		for (int i : testString) {
			if (i != 0) {
				return false;
			}
		}
		return true;
	}

	public boolean isMaxTestString(ArrayList<Integer> testString) throws IllegalArgumentException {
		if (!this.isSimulating) {
			this.validateTestString(testString);
		}

		int index = this.getMaxInputIndex();
		for (int i : testString) {
			if (i != index) {
				return false;
			}
		}
		return true;
	}

	public void printMachine() {
		System.out.print("\nInput alphabet:");
		for (int i = 0; i < this.getInputAlphabetSize(); i++) {
			System.out.print(' ' + this.inputAlphabet[i]);
		}

		if (this.getNumAcceptingStates() == 0) {
			System.out.print("\nEvery state is a reject state.");
		} else if (this.getNumAcceptingStates() == this.getNumStates()) {
			System.out.print("\nEvery state is an accept state.");
		} else {
			System.out.print("\nAccepting states:");
			for (int i = 0; i < this.getNumStates(); i++) {
				if (this.accepting[i]) {
					System.out.print(' ' + i);
				}
			}
		}

		System.out.println("\n\nNumber of defined transitions: " + this.getNumDefinedTransitions());
		System.out.println("Transition table:");
		this.printTransitions(true);
	}

	public String printSimulationInfo() {
		if (this.count) {
			System.out.print('\n');
			if (this.getActualStringCount() == 1) {
				System.out.println("There was only 1 string to test.");
			} else {
				if (this.getMaxStringCount() != this.getActualStringCount()) {
					System.out
							.println("There were only " + DFA.comma(this.getActualStringCount()) + " strings to test.");
				}

				if (this.getAcceptCount() == this.getActualStringCount()) {
					System.out.println("All of the tested strings were accepted.");
				} else if (this.getRejectCount() == this.getActualStringCount()) {
					System.out.println("All of the tested strings were rejected.");
				} else {
					if (this.getAcceptCount() != 0) {
						if (this.getAcceptCount() == 1) {
							System.out.println("1 string was accepted.");
						} else {
							System.out.println(DFA.comma(this.getAcceptCount()) + " strings were accepted.");
						}
					}

					if (this.getRejectCount() != 0) {
						if (this.getRejectCount() == 1) {
							System.out.println("1 string was rejected.");
						} else {
							System.out.println(DFA.comma(this.getRejectCount()) + " strings were rejected.");
						}
					}
				}
			}
		}
		System.out.println("\nThe entire process took " + this.getTime() + ".\n");
		return this.getTime();
	}

	/*
	 * throw an IllegalArgumentException with padding "\n" so that the exception message appears
	 * separately on the System.err PrintStream.
	 */
	private static void illegalArg(String cause) throws IllegalArgumentException {
		throw new IllegalArgumentException("\n\n" + cause + '\n');
	}

	private void illegalArg() throws IllegalArgumentException {
		DFA.illegalArg(this.getCause());
	}

	// recursively add a ',' after every 3 characters of s starting from the right
	public static String comma(String s) throws NullPointerException {
		if (s.length() <= 3) {
			return s;
		}
		return DFA.comma(s.substring(0, s.length() - 3)) + ',' + s.substring(s.length() - 3);
	}

	public static String comma(int i) {
		return DFA.comma(Integer.toString(i));
	}

	public static String formatTime(long time) {
		if (time < 0) {
			DFA.staticCause = "Given value of time(" + time + ") is negative.";
			DFA.illegalArg(DFA.getStaticCause());
		} else if (time == 0) {
			return "nearly 0 milliseconds";
		}

		int millis = (int) (time % DFA.MILLISECONDS_PER_SECOND);
		Long seconds = (long) 0;
		Integer minutes = 0, hours = 0, days = 0;

		if (time >= DFA.MILLISECONDS_PER_SECOND) {
			seconds = time / DFA.MILLISECONDS_PER_SECOND;
			DFA.timeCalculate(seconds, DFA.SECONDS_PER_DAY, days);
			DFA.timeCalculate(seconds, DFA.SECONDS_PER_HOUR, hours);
			DFA.timeCalculate(seconds, DFA.SECONDS_PER_MINUTE, minutes);
		}

		StringBuilder s = new StringBuilder("");
		DFA.timeAppend(s, days, "day");
		DFA.timeAppend(s, hours, "hour");
		DFA.timeAppend(s, minutes, "minute");
		DFA.timeAppend(s, DFA.safeCastLong2Int(seconds), "second");
		DFA.timeAppend(s, millis, "millisecond");
		String output = s.toString();
		output = output.replaceAll("(and)", " ");
		return output.trim().replaceAll("( )+", "and");
	}

	@SuppressWarnings("unused")
	private static void timeCalculate(Long seconds, int bound, Integer remainder) {
		if (seconds >= bound) {
			remainder = (int) (seconds / bound);
			seconds %= bound;
		}
	}

	private static void timeAppend(StringBuilder s, int val, String unit) {
		if (val == 1) {
			s.append("1 " + unit);
		} else if (val != 0) {
			s.append(val + ' ' + unit + 's');
		}
		s.append(s.length() != 0 ? " and " : "");
	}

	// returns 0 for long values out of Integer bounds
	public static int safeCastLong2Int(long l) {
		if (l >= Integer.MIN_VALUE && l <= Integer.MAX_VALUE) {
			return ((int) l);
		}
		return 0;
	}

	public static long nano2Milli(long nanoSeconds) throws IllegalArgumentException {
		if (nanoSeconds < 0) {
			DFA.staticCause = "Given time in nanoseconds(" + nanoSeconds + ") is negative.";
			DFA.illegalArg(DFA.getStaticCause());
		}
		return Math.round((double) nanoSeconds / DFA.NANOSECONDS_PER_MILLISECOND);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		} else if (!(obj instanceof DFA)) {
			return false;
		}
		DFA other = (DFA) obj;

		if (this.getNumStates() != other.getNumStates()) {
			return false;
		} else if (this.getInputAlphabetSize() != other.getInputAlphabetSize()) {
			return false;
		} else if (this.getNumAcceptingStates() != other.getNumAcceptingStates()) {
			return false;
		} else if (!this.inputIndex.equals(other.inputIndex)) {
			return false;
		}

		for (int i = 0; i < this.getNumAcceptingStates(); i++) {
			if (this.accepting[i] != other.accepting[i]) {
				return false;
			}
		}

		for (int i = 0; i < this.getNumStates(); i++) {
			for (int j = 0; j < this.getInputAlphabetSize(); j++) {
				if (this.nextState[i][j] != other.nextState[i][j]) {
					return false;
				}
			}
		}

		return true;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + Arrays.hashCode(this.accepting);
		result = prime * result + this.getTotalNumTransitions();
		result = prime * result + Arrays.deepHashCode(this.defined);
		result = prime * result + Arrays.hashCode(this.inputAlphabet);
		result = prime * result + this.getInputAlphabetSize();
		result = prime * result + this.inputIndex.hashCode();
		result = prime * result + this.getNumAcceptingStates();
		result = prime * result + Arrays.deepHashCode(this.nextState);
		result = prime * result + this.getNumDefinedTransitions();
		result = prime * result + this.getNumStates();
		return result;
	}

	@Override
	public String toString() {
		if (!this.strChange) {
			return this.savedStr;
		}
		StringBuilder output = new StringBuilder("");

		// first line
		output.append(this.getNumStates() + ' ' + this.getInputAlphabetSize() + ' ' + this.getNumAcceptingStates() + ' '
				+ this.getNumDefinedTransitions() + '\n');

		// second line
		for (int i = 0; i < this.getInputAlphabetSize(); i++) {
			output.append(this.inputAlphabet[i] + (i != this.getInputAlphabetSize() - 1 ? ' ' : ""));
		}
		output.append('\n');

		// third line
		int count = 0;
		for (int i = 0; i < this.getNumStates(); i++) {
			if (this.accepting[i]) {
				output.append(i + (++count != this.getNumAcceptingStates() ? " " : ""));
			}
		}
		output.append('\n');

		// transition lines
		String[] definedTransitions = this.getDefinedTransitions();
		for (int i = 0; i < definedTransitions.length; i++) {
			output.append(definedTransitions[i] + '\n');
		}

		// command line
		StringBuilder command = new StringBuilder("");
		if (this.getMaxStringCount() == 0) {
			output.append('0');
		} else {
			command.append(
					(this.getMaxStringCount() == DFA.DEFAULT_MAX_STRING_COUNT ? DFA.DEFAULT : this.getMaxStringCount())
							+ " ");
			command.append((this.getMinLength() == DFA.DEFAULT_MIN_LENGTH ? DFA.DEFAULT : this.getMinLength()) + " ");
			command.append((this.getMaxLength() == DFA.DEFAULT_MAX_LENGTH ? DFA.DEFAULT : this.getMaxLength()) + " ");
			command.append(this.getInitialString().isEmpty() ? DFA.DEFAULT : this.getInitialString());
			output.append(this.commandLine(command.toString()));
		}

		// comments
		output.append("\n" + (this.getIncludeComments() ? this.comments : ""));

		this.strChange = false;
		return (this.savedStr = output.toString());
	}

	private String commandLine(String command) {
		while (command.endsWith(DFA.DEFAULT)) {
			int index = command.lastIndexOf(DFA.DEFAULT);
			// remove last occurrence of | default| or just |default|
			command = index != 0 ? command.substring(0, index - 1) : "";
		}
		if (!command.isEmpty()) {
			String[] s = command.split(DFA.DELIMITER_STRING);
			if (s.length == 3 && this.getMinLength() == DFA.DEFAULT_MIN_LENGTH) {
				// special case where the minLength is its default value
				// and the command line is: |maxStringCount minLength maxLength|
				// minLength(s[1]) can be removed since we can accomplish
				// the same effect by just putting maxLength
				command = s[0] + ' ' + s[2];
			} else if (s.length == 2) {
				// special case where the maxLength has been removed but
				// the minLength hasn't. To avoid having the constructor
				// interpret the minLength as the maxLength, we have to
				// append a DFA.DEFAULT
				command += ' ' + DFA.DEFAULT;
			}
		}
		return command;
	}

	public static boolean isValidFileName(String fileName) {
		if (fileName == null || fileName.isEmpty()) {
			return false;
		}

		StringBuilder name = new StringBuilder(fileName.charAt(0));
		for (int i = 1; i < fileName.length(); i++) {
			char c = fileName.charAt(i);
			if (c != '.' && c != '-' && c != '_') {
				name.append(c);
			}
		}
		return name.toString().matches("(\\w)+");
	}

	public void validateFileName(String fileName) throws IllegalArgumentException {
		if (!DFA.isValidFileName(fileName)) {
			this.cause = "Given file name(" + fileName + ") isn't valid.";
			this.illegalArg();
		}
	}

	@SuppressWarnings("resource")
	public String saveToFile(String fileName, boolean overwrite) throws IllegalArgumentException, IOException {
		this.validateFileName(fileName);
		this.overwrote = false;

		String content = this.toString(), result = this.machines.get(fileName);
		if (result != null) {
			if (!(this.overwrote = overwrite)) {
				System.out.println("A file with name " + fileName + " already exists.");
				return content;
			}
		} else {
			result = content;
		}

		try {
			PrintWriter writer = new PrintWriter(fileName + ".txt", "UTF-8");
			writer.print(content);
			writer.close();
			this.machines.put(fileName, content);
			return result;
		} catch (IOException ex) {
			this.overwrote = false;
			this.cause = "Couldn't save the description of the current machine to a file with name " + fileName + '.';
			throw new IOException("\n\n" + this.getCause() + '\n');
		}
	}

	public String saveToFile(String fileName) throws IllegalArgumentException, IOException {
		return this.saveToFile(fileName, false);
	}

	public String saveToFile(boolean overwrite) throws IllegalArgumentException, IOException {
		return this.saveToFile(DFA.DEFAULT_FILE_NAME, overwrite);
	}

	public String saveToFile() throws IllegalArgumentException, IOException {
		return this.saveToFile(DFA.DEFAULT_FILE_NAME, false);
	}

	@SuppressWarnings("null")
	public static DFA main(DFA m, String[] args, boolean stdin) throws IllegalArgumentException {
		DFA machine = m;
		int eval = 0;
		boolean success = machine != null, save = false;
		String s = null;

		if (args != null) {
			for (int i = 0; i < args.length; i++) {
				if (args[i] == null || args[i].isEmpty()) {
					continue;
				}

				if ((s = DFA.lower(args[i])) != null) {
					save = save || s.equals(DFA.SAVE);
					stdin = stdin || s.equals(DFA.STDIN);
					if (s.equals(DFA.TRUE_1) || s.equals(DFA.TRUE_2)) {
						eval++;
					} else if (s.equals(DFA.FALSE_1) || s.equals(DFA.FALSE_2)) {
						eval--;
					}
				}

				if (!success && !stdin) {
					try { // if no exception is thrown then the result is necessarily true
						success = (machine = new DFA(args[i], true)) != null;
					} catch (FileNotFoundException ex) {
						try { // if no exception is thrown then the result is necessarily true
							success = (machine = new DFA((args[i] + ".txt"), true)) != null;
						} catch (FileNotFoundException ex1) {
						}
					}
				}

				if (!success && !stdin && DFA.DEFAULT_FILE_NAME.equals(s)) {
					try { // if no exception is thrown then the result is necessarily true
						success = (machine = new DFA(DFA.DEFAULT_FILE_NAME, true)) != null;
					} catch (FileNotFoundException ex) {
						try { // if no exception is thrown then the result is necessarily true
							success = (machine = new DFA((DFA.DEFAULT_FILE_NAME + ".txt"), true)) != null;
						} catch (FileNotFoundException ex1) {
						}
					}
				}
			}
		}
		machine = !success ? new DFA() : machine;
		machine.simulate(eval >= 0);

		if (save) {
			try {
				s = machine.saveToFile(true);
			} catch (IOException ex) {
				s = null;
			}
			System.out.println("\n--------------------------------------------------\n");
			if (s == null) {
				System.out.println(machine.getCause());
			} else {
				if (machine.getOverwrote()) {
					System.out.println("The description of the current machine has been overwritten onto "
							+ DFA.DEFAULT_FILE_NAME + ".txt in the same directory.");
					System.out.println("Its previous contents were:\n" + s);
				} else {
					System.out.println("The description of the current machine was saved to " + DFA.DEFAULT_FILE_NAME
							+ ".txt in the same directory.");
				}
			}
		}

		return machine;
	}

	public static DFA main(DFA m, String[] args) throws IllegalArgumentException {
		return DFA.main(m, args, false);
	}

	public static DFA main(DFA m, boolean stdin) throws IllegalArgumentException {
		return DFA.main(m, null, stdin);
	}

	public static DFA main(String[] args, boolean stdin) throws IllegalArgumentException {
		return DFA.main(null, args, stdin);
	}

	public static DFA main(DFA m) throws IllegalArgumentException {
		return DFA.main(m, null, false);
	}

	// the version of main called by the Java compiler
	public static void main(String[] args) throws IllegalArgumentException {
		DFA.main(null, args, false);
	}

	public static DFA main(boolean stdin) throws IllegalArgumentException {
		return DFA.main(null, null, stdin);
	}

	public static DFA main() throws IllegalArgumentException {
		return DFA.main(true);
	}

	public static DFA main2(String fileName, boolean print, boolean save) throws IllegalArgumentException {
		String[] args = { fileName, Boolean.toString(print), save ? DFA.SAVE : null };
		return DFA.main(null, args);
	}

	public static DFA main2(String fileName, boolean print) throws IllegalArgumentException {
		return DFA.main2(fileName, print, false);
	}

	public static DFA main2(String fileName) throws IllegalArgumentException {
		return DFA.main2(fileName, false);
	}

	public static DFA main3(String machineDescription, boolean print, boolean save) throws IllegalArgumentException {
		DFA m = new DFA(machineDescription);
		String[] args = { Boolean.toString(print), save ? DFA.SAVE : null };
		return DFA.main(m, args, true);
	}

	public static DFA main3(String machineDescription, boolean print) throws IllegalArgumentException {
		return DFA.main3(machineDescription, print, false);
	}

	public static DFA main3(String machineDescription) throws IllegalArgumentException {
		return DFA.main3(machineDescription, false);
	}
}
