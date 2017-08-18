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

public class TMSS {
	/*
	 * for simplicity, all methods only throw IllegalArgumentException so that only one type of
	 * exception need be handled but in general, it's better practice to throw other types of exceptions
	 * when appropriate such as NullPointerException, IllegalStateException and etc.
	 */

	public static final char DELIMITER_CHAR = ' ';
	public static final String DELIMITER_STRING = Character.toString(TMSS.DELIMITER_CHAR);

	public static final int MIN_NUM_STATES = 3, MAX_NUM_STATES = 10000, MIN_INPUT_ALPHABET_SIZE = 1,
			MAX_TAPE_ALPHABET_SIZE = 1000;
	private int numStates, tapeAlphabetSize, inputAlphabetSize;
	// tape/input Index maps tape/input Characters to indices
	private HashMap<String, Integer> tapeIndex, inputIndex;
	private String[] tapeAlphabet, inputAlphabet;

	public static final String WHITESPACE_REGEX = "(\\s)+";
	private static final Pattern WHITESPACE_PATTERN = Pattern.compile(TMSS.WHITESPACE_REGEX);

	// these three arrays are used to store the transition function
	private int[][] nextState, charToWriteIndex;
	private String[][] direction;
	// array used to keep track of defined transitions
	private boolean[][] defined;
	private int totalNumTransitions, numDefinedTransitions;
	private int[] stateNumDefined;

	public static final String BLANK = "blank";
	private static final String[] SPECIAL_TAPE_CHARS = { TMSS.BLANK };
	public static final int NUM_SPECIAL_TAPE_CHARS = TMSS.SPECIAL_TAPE_CHARS.length,
			MAX_INPUT_ALPHABET_SIZE = TMSS.MAX_TAPE_ALPHABET_SIZE - TMSS.NUM_SPECIAL_TAPE_CHARS,
			MIN_TAPE_ALPHABET_SIZE = TMSS.MIN_INPUT_ALPHABET_SIZE + TMSS.NUM_SPECIAL_TAPE_CHARS;

	public static final String LEFT = "L", RIGHT = "R", STILL = "S";
	private String[] validDirections;
	public static final boolean DEFAULT_INCLUDE_STILL = true;
	private boolean includeStill;
	private int stillCount;

	public static final String DEFAULT = "default";

	public static final int DEFAULT_MAX_STRING_COUNT = 100, MAX_STRINGS_COUNT = 100000;
	private int maxStringCount, actualStringCount, acceptCount, rejectCount, infiniteCount;
	/*
	 * count holds whether maxStringCount is greater than 1 or not so that the boolean is not
	 * reevaluated every time that it is needed. checkStringsCount is used to determine when to estimate
	 * the number of strings to test(stringsCount) so that the time consuming process isn't repeatedly
	 * performed by the testString length mutator methods
	 */
	private boolean count, checkStringsCount = true;
	/*
	 * maps testString to output:stepCount:elapsedProcessTime. always construct results with
	 * initialCapacity of maxStringCount so that the need for resizing, rehashing, ... is greatly
	 * reduced
	 */
	private HashMap<ArrayList<Integer>, String> results;

	public static final int DEFAULT_MIN_LENGTH = 0, DEFAULT_MAX_LENGTH = 5;
	private int minLength, maxLength;

	public static final long DEFAULT_MAX_STEPS = Long.MAX_VALUE;
	private long maxSteps, stepCount;

	public static final String DEFAULT_INITIAL_STRING = "";
	private static final ArrayList<Integer> DEFAULT_INITIAL_ARRAY = new ArrayList<Integer>();
	private String initialString;
	private ArrayList<Integer> initialArray = TMSS.DEFAULT_INITIAL_ARRAY;

	public static final boolean DEFAULT_TRACE = false;
	private boolean trace;
	// 1 hour in milliseconds
	public static final long MIN_PROCESS_TIME = 0, DEFAULT_MAX_PROCESS_TIME = 3600000;
	public static final boolean DEFAULT_TIME_LIMIT = false;
	private boolean timeLimit;
	private long maxProcessTime, nanoMaxProcessTime, elapsedProcessTime;

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

	public static final int LINE_1_NUM_ENTRIES = 3, LINE_3_NUM_ENTRIES = 1, COMMAND_LINE_MAX_NUM_ENTRIES = 8;

	// every month is 30.5 days on average
	public static final int SECONDS_PER_MONTH = 18446400, SECONDS_PER_WEEK = 604800, SECONDS_PER_DAY = 86400,
			SECONDS_PER_HOUR = 3600, SECONDS_PER_MINUTE = 60, MILLISECONDS_PER_SECOND = 1000,
			NANOSECONDS_PER_MILLISECOND = 1000000;
	public static final long MAX_PROCESS_TIME = Long.MAX_VALUE / TMSS.NANOSECONDS_PER_MILLISECOND;
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

		int prevNumStates = this.getNumStates(), a = this.getAcceptState(), t = this.getTapeAlphabetSize();
		int[][] nextState = null;
		int[][] charToWriteIndex = null;
		String[][] direction = null;
		boolean[][] defined = null;

		if (copyValidTransitions) {
			nextState = new int[a][t];
			charToWriteIndex = new int[a][t];
			direction = new String[a][t];
			defined = new boolean[a][t];
			for (int i = 0; i < a; i++) {
				for (int j = 0; j < t; j++) {
					nextState[i][j] = this.nextState[i][j];
					charToWriteIndex[i][j] = this.charToWriteIndex[i][j];
					direction[i][j] = this.direction[i][j];
					defined[i][j] = this.defined[i][j];
				}
			}
		}

		a = (this.numStates = numStates) - 2; // new accept state
		this.totalNumTransitions = a * t;
		this.stateNumDefined = new int[a];
		this.initializeTransitions();

		if (copyValidTransitions) {
			int min = Math.min(numStates, prevNumStates);

			for (int i = 0; i < a; i++) {
				for (int j = 0; j < t; j++) {
					// increase in number of states
					if (min == prevNumStates) {
						// copy transition only if initial state existed
						if (i < prevNumStates - 2) {
							this.nextState[i][j] = nextState[i][j];
							this.charToWriteIndex[i][j] = charToWriteIndex[i][j];
							this.direction[i][j] = direction[i][j];
							if (defined[i][j]) {
								this.defined[i][j] = true;
								this.numDefinedTransitions++;
							}
						}
					} else { // decrease in number of states
						int state = nextState[i][j];
						// copy transition only if final state is still valid
						if (state < numStates) {
							this.nextState[i][j] = state;
							this.charToWriteIndex[i][j] = charToWriteIndex[i][j];
							this.direction[i][j] = direction[i][j];
							if (defined[i][j]) {
								this.defined[i][j] = true;
								this.numDefinedTransitions++;
							}
						}
					}
				}
			}
		}

		return this.getNumStates();
	}

	public int setNumStates(int numStates) throws IllegalArgumentException {
		return this.setNumStates(numStates, false);
	}

	public static boolean isValidNumStates(int numStates) {
		return (numStates >= TMSS.MIN_NUM_STATES && numStates <= TMSS.MAX_NUM_STATES);
	}

	public static String getNumStatesRange() {
		return ('[' + TMSS.MIN_NUM_STATES + ", " + TMSS.MAX_NUM_STATES + ']');
	}

	public int validateNumStates(int numStates) throws IllegalArgumentException {
		if (!TMSS.isValidNumStates(numStates)) {
			this.cause = "Given number of states(" + numStates + ") isn't in the range of " + TMSS.getNumStatesRange()
					+ '.';
			this.illegalArg();
		}
		return numStates;
	}

	public int getAcceptState() {
		return (this.getNumStates() - 2);
	}

	public int getRejectState() {
		return (this.getNumStates() - 1);
	}

	public boolean isValidInitialState(int initialState) {
		return (initialState >= 0 && initialState < this.getAcceptState());
	}

	public String getInitialStateRange() {
		return ("[0, " + (this.getAcceptState() - 1) + ']');
	}

	public int validateInitialState(int initialState) {
		if (!this.isValidInitialState(initialState)) {
			this.cause = "Given initial state";
			if (this.isScanning) {
				this.cause += " on line " + this.lineNumber;
			}
			this.cause += '(' + initialState + ") isn't in the range of " + this.getInitialStateRange() + '.';
			this.illegalArg();
		}
		return initialState;
	}

	public boolean isValidFinalState(int finalState) {
		return (finalState >= 0 && finalState <= this.getRejectState());
	}

	public String getFinalStateRange() {
		return ("[0, " + this.getRejectState() + ']');
	}

	public int validateFinalState(int finalState) {
		if (!this.isValidFinalState(finalState)) {
			this.cause = "Given final state";
			if (this.isScanning) {
				this.cause += " on line " + this.lineNumber;
			}
			this.cause += '(' + finalState + ") isn't in the range of " + this.getFinalStateRange() + '.';
			this.illegalArg();
		}
		return finalState;
	}

	public int getTapeAlphabetSize() {
		return this.tapeAlphabetSize;
	}

	public int getBlankIndex() {
		return (this.getTapeAlphabetSize() - 1);
	}

	public boolean isValidTapeCharIndex(int index) {
		return (index >= 0 && index <= this.getBlankIndex());
	}

	public String getTapeCharIndexRange() {
		return ("[0, " + this.getBlankIndex() + ']');
	}

	public int validateTapeCharIndex(int index) throws IllegalArgumentException {
		if (!this.isValidTapeCharIndex(index)) {
			this.cause = "Given tape character index(" + index + ") isn't in the range of "
					+ this.getTapeCharIndexRange() + '.';
			this.illegalArg();
		}
		return index;
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

	public boolean isValidTapeChar(String s) {
		if (s == null || TMSS.WHITESPACE_PATTERN.matcher(s).find()) {
			return false;
		}
		return this.tapeIndex.containsKey(s);
	}

	public int tapeCharIndexOf(String s) {
		Integer index = this.tapeIndex.get(s);
		return (index != null ? index : -1);
	}

	public int validateTapeChar(String s, boolean isInitial) throws IllegalArgumentException {
		int index = this.tapeCharIndexOf(s);
		if (index == -1) {
			this.cause = "Given " + (isInitial ? "initial" : "final") + " character";
			if (this.isScanning) {
				this.cause += " on line " + this.lineNumber;
			}
			this.cause += '(' + s + ") isn't a valid tape character.";
			this.illegalArg();
		}
		return index;
	}

	public int validateTapeChar(String s) throws IllegalArgumentException {
		return this.validateTapeChar(s, true);
	}

	@SuppressWarnings("null")
	public static boolean isSpecialTapeChar(String s) throws IllegalArgumentException {
		if (s == null) {
			TMSS.staticCause = "Given tape character is null.";
			TMSS.illegalArg(TMSS.getStaticCause());
		}
		return s.toLowerCase().contains(TMSS.BLANK);
	}

	public String getTapeChar(int index) throws IllegalArgumentException {
		return this.tapeAlphabet[this.validateTapeCharIndex(index)];
	}

	private String[] getTapeAlphabet(boolean isConstructing) {
		String[] result = isConstructing ? new String[this.getBlankIndex()] : new String[this.getTapeAlphabetSize()];
		System.arraycopy(this.tapeAlphabet, 0, result, 0, result.length);
		return result;
	}

	public String[] getTapeAlphabet() {
		return this.getTapeAlphabet(false);
	}

	public static String[] getDefaultTapeAlphabet() {
		String[] tapeAlphabet = { "0", "1", "X" };
		return tapeAlphabet;
	}

	public boolean isValidInputChar(String s) {
		if (s == null || TMSS.WHITESPACE_PATTERN.matcher(s).find()) {
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
			this.cause = "Given input character(" + s + ") isn't a valid input character.";
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

	public Object[] setAlphabet(int tapeAlphabetSize, int inputAlphabetSize, String[] tapeAlphabet)
			throws IllegalArgumentException {
		String[] inputAlphabet = this.validateAlphabet(tapeAlphabetSize, inputAlphabetSize, tapeAlphabet);
		this.inputAlphabet = new String[this.inputAlphabetSize = inputAlphabetSize];
		System.arraycopy(inputAlphabet, 0, this.inputAlphabet, 0, inputAlphabetSize);

		this.inputIndex = new HashMap<String, Integer>(inputAlphabetSize);
		for (int i = 0; i < inputAlphabetSize; i++) {
			this.inputIndex.put(this.inputAlphabet[i], i);
		}

		this.tapeAlphabet = new String[this.tapeAlphabetSize = tapeAlphabetSize];
		// copy sorted input alphabet into (sorted) tape alphabet
		System.arraycopy(this.inputAlphabet, 0, this.tapeAlphabet, 0, inputAlphabetSize);
		String s;
		for (int i = 0, index = inputAlphabetSize; index < this.getBlankIndex(); i++) {
			if (this.inputCharIndexOf(s = tapeAlphabet[i]) == -1) {
				// copy tapeAlphabet characters that aren't in the inputAlphabet in sorted
				// order after the inputAlphabet characters
				this.tapeAlphabet[index++] = s;
			}
		}
		System.arraycopy(TMSS.SPECIAL_TAPE_CHARS, 0, this.tapeAlphabet, this.getBlankIndex(),
				TMSS.NUM_SPECIAL_TAPE_CHARS); // copy special tape chars

		this.tapeIndex = new HashMap<String, Integer>(tapeAlphabetSize);
		for (int i = 0; i < tapeAlphabetSize; i++) {
			this.tapeIndex.put(this.tapeAlphabet[i], i);
		}

		this.totalNumTransitions = this.getAcceptState() * tapeAlphabetSize;
		this.initializeTransitions();

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

	public boolean isValidAlphabet(int tapeAlphabetSize, int inputAlphabetSize, String[] tapeAlphabet) {
		try { // if no exception is thrown then the result is necessarily true
			return (this.validateAlphabet(tapeAlphabetSize, inputAlphabetSize, tapeAlphabet) != null);
		} catch (IllegalArgumentException ex) {
			return false;
		}
	}

	@SuppressWarnings("null")
	public String[] validateAlphabet(int tapeAlphabetSize, int inputAlphabetSize, String[] tapeAlphabet)
			throws IllegalArgumentException {
		this.validateTapeAlphabetSize(tapeAlphabetSize, inputAlphabetSize);
		if (tapeAlphabet == null || tapeAlphabet.length != tapeAlphabetSize - TMSS.NUM_SPECIAL_TAPE_CHARS) {
			this.cause = "Given tape alphabet isn't valid.";
			this.illegalArg();
		}

		HashMap<String, Integer> tapeIndex = new HashMap<String, Integer>();
		String tapeChar;
		for (int i = 0; i < tapeAlphabet.length; i++) {
			if ((tapeChar = tapeAlphabet[i]) == null) {
				this.cause = "Given tape alphabet isn't valid since it contains null at index " + i + '.';
				this.illegalArg();
			} else if (tapeChar.isEmpty()) {
				this.cause = '"' + tapeChar + "\" isn't valid since it's the empty string.";
				this.illegalArg();
			} else if (TMSS.WHITESPACE_PATTERN.matcher(tapeChar).find()) {
				this.cause = '"' + tapeChar + "\" isn't valid since it contains whitespace.";
				this.illegalArg();
			} else if (tapeIndex.containsKey(tapeChar)) {
				this.cause = '"' + tapeChar + "\" has been defined more than once.";
				this.illegalArg();
			} else if (TMSS.isSpecialTapeChar(tapeChar)) {
				this.cause = '"' + tapeChar + "\" isn't valid since it is/contains a special tape character.";
				this.illegalArg();
			}
			tapeIndex.put(tapeChar, i);
		}

		String[] inputAlphabet = new String[inputAlphabetSize];
		System.arraycopy(tapeAlphabet, 0, inputAlphabet, 0, inputAlphabetSize);
		Arrays.sort(inputAlphabet);
		this.validateInputAlphabet(inputAlphabet);
		Arrays.sort(tapeAlphabet);
		return inputAlphabet;
	}

	// even if it returns true, tapeAlphabetSize isn't necessarily valid since
	// inputAlphabetSize hasn't been taken into account
	public static boolean isValidTapeAlphabetSize(int tapeAlphabetSize) {
		return (tapeAlphabetSize >= TMSS.MIN_TAPE_ALPHABET_SIZE && tapeAlphabetSize <= TMSS.MAX_TAPE_ALPHABET_SIZE);
	}

	// the absolute tapeAlphabetSize range without taking the value of
	// inputAlphabetSize into account
	public static String getTapeAlphabetSizeRange() {
		return ('[' + TMSS.MIN_TAPE_ALPHABET_SIZE + ", " + TMSS.MAX_TAPE_ALPHABET_SIZE + ']');
	}

	public int validateTapeAlphabetSize(int tapeAlphabetSize) throws IllegalArgumentException {
		if (!TMSS.isValidTapeAlphabetSize(tapeAlphabetSize)) {
			this.cause = "Given tape alphabet size(" + tapeAlphabetSize + ") isn't in the range of "
					+ TMSS.getTapeAlphabetSizeRange() + '.';
			this.illegalArg();
		}
		return tapeAlphabetSize;
	}

	public static boolean isValidInputAlphabetSize(int inputAlphabetSize) {
		return (inputAlphabetSize >= TMSS.MIN_INPUT_ALPHABET_SIZE && inputAlphabetSize <= TMSS.MAX_INPUT_ALPHABET_SIZE);
	}

	public static String getInputAlphabetSizeRange() {
		return ('[' + TMSS.MIN_INPUT_ALPHABET_SIZE + ", " + TMSS.MAX_INPUT_ALPHABET_SIZE + ']');
	}

	public static int validateInputAlphabetSize(int inputAlphabetSize) throws IllegalArgumentException {
		if (!TMSS.isValidInputAlphabetSize(inputAlphabetSize)) {
			TMSS.staticCause = "Given input alphabet size(" + inputAlphabetSize + ") isn't in the range of "
					+ TMSS.getInputAlphabetSizeRange() + '.';
			TMSS.illegalArg(TMSS.getStaticCause());
		}
		return inputAlphabetSize;
	}

	public static boolean isValidTapeAlphabetSize(int tapeAlphabetSize, int inputAlphabetSize)
			throws IllegalArgumentException {
		TMSS.validateInputAlphabetSize(inputAlphabetSize);
		return (tapeAlphabetSize >= inputAlphabetSize + TMSS.NUM_SPECIAL_TAPE_CHARS
				&& tapeAlphabetSize <= TMSS.MAX_TAPE_ALPHABET_SIZE);
	}

	public static String getTapeAlphabetSizeRange(int inputAlphabetSize) throws IllegalArgumentException {
		TMSS.validateInputAlphabetSize(inputAlphabetSize);
		return ('[' + (inputAlphabetSize + TMSS.NUM_SPECIAL_TAPE_CHARS) + ", " + TMSS.MAX_TAPE_ALPHABET_SIZE + ']');
	}

	public void validateTapeAlphabetSize(int tapeAlphabetSize, int inputAlphabetSize) throws IllegalArgumentException {
		try {
			if (!TMSS.isValidTapeAlphabetSize(tapeAlphabetSize, inputAlphabetSize)) {
				this.cause = "Given tape alphabet size(" + tapeAlphabetSize + ") isn't in the range of "
						+ TMSS.getTapeAlphabetSizeRange(inputAlphabetSize) + '.';
				this.illegalArg();
			}
		} catch (IllegalArgumentException ex) {
			this.cause = TMSS.getStaticCause();
			this.illegalArg();
		}
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
		if (!TMSS.isValidInputAlphabet(s)) {
			this.cause = "Given input alphabet isn't valid since two of its characters start the same way.";
			this.illegalArg();
		}
		return s;
	}

	private Object[] getInitialStringRepresentations() {
		Object[] result = { this.getInitialArray(), this.getInitialString(), this.toString(this.initialArray, true) };
		return result;
	}

	public int getNextState(int initialState, String initialChar) throws IllegalArgumentException {
		int initialCharIndex = (int) (this.validateTransition(initialState, initialChar)[2]);
		return this.nextState[initialState][initialCharIndex];
	}

	public int[][] getNextState() {
		int a = this.getAcceptState(), t = this.getTapeAlphabetSize();
		int[][] result = new int[a][t];
		for (int i = 0; i < a; i++) {
			System.arraycopy(this.nextState[i], 0, result[i], 0, t);
		}
		return result;
	}

	public int getCharToWriteIndex(int initialState, String initialChar) throws IllegalArgumentException {
		int initialCharIndex = (int) (this.validateTransition(initialState, initialChar)[2]);
		return this.charToWriteIndex[initialState][initialCharIndex];
	}

	public int[][] getCharToWriteIndex() {
		int a = this.getAcceptState(), t = this.getTapeAlphabetSize();
		int[][] result = new int[a][t];
		for (int i = 0; i < a; i++) {
			System.arraycopy(this.charToWriteIndex[i], 0, result[i], 0, t);
		}
		return result;
	}

	public String getCharToWrite(int initialState, String initialChar) throws IllegalArgumentException {
		int initialCharIndex = (int) (this.validateTransition(initialState, initialChar)[2]);
		return this.tapeAlphabet[this.charToWriteIndex[initialState][initialCharIndex]];
	}

	public String[][] getCharToWrite() {
		int a = this.getAcceptState(), t = this.getTapeAlphabetSize();
		String[][] result = new String[a][t];
		for (int i = 0; i < a; i++) {
			for (int j = 0; j < t; j++) {
				result[i][j] = this.tapeAlphabet[this.charToWriteIndex[i][j]];
			}
		}
		return result;
	}

	public String getDirection(int initialState, String initialChar) throws IllegalArgumentException {
		int initialCharIndex = (int) (this.validateTransition(initialState, initialChar)[2]);
		return this.direction[initialState][initialCharIndex];
	}

	public String[][] getDirection() {
		int a = this.getAcceptState(), t = this.getTapeAlphabetSize();
		String[][] result = new String[a][t];
		for (int i = 0; i < a; i++) {
			System.arraycopy(this.direction[i], 0, result[i], 0, t);
		}
		return result;
	}

	public boolean getDefined(int initialState, String initialChar) throws IllegalArgumentException {
		int initialCharIndex = (int) (this.validateTransition(initialState, initialChar)[2]);
		return this.defined[initialState][initialCharIndex];
	}

	public boolean[][] getDefined() {
		int a = this.getAcceptState(), t = this.getTapeAlphabetSize();
		boolean[][] result = new boolean[a][t];
		for (int i = 0; i < a; i++) {
			System.arraycopy(this.defined[i], 0, result[i], 0, t);
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
		return this.stateNumDefined[this.validateInitialState(initialState)];
	}

	public int[] getStateNumDefined() {
		int[] result = new int[this.getAcceptState()];
		System.arraycopy(this.stateNumDefined, 0, result, 0, result.length);
		return result;
	}

	public static String[] getSpecialTapeChars() {
		String[] result = new String[TMSS.NUM_SPECIAL_TAPE_CHARS];
		System.arraycopy(TMSS.SPECIAL_TAPE_CHARS, 0, result, 0, result.length);
		return result;
	}

	private String getTransition(int initialState, int initialCharIndex, boolean format) {
		if (format) {
			return ("delta(" + initialState + ',' + this.tapeAlphabet[initialCharIndex] + ") = ("
					+ this.nextState[initialState][initialCharIndex] + ','
					+ this.tapeAlphabet[this.charToWriteIndex[initialState][initialCharIndex]] + ','
					+ this.direction[initialState][initialCharIndex] + ')');
		}
		return (initialState + ' ' + this.tapeAlphabet[initialCharIndex] + ' '
				+ this.nextState[initialState][initialCharIndex] + ' '
				+ this.tapeAlphabet[this.charToWriteIndex[initialState][initialCharIndex]] + ' '
				+ this.direction[initialState][initialCharIndex]);
	}

	public String getTransition(int initialState, String initialChar, boolean format, boolean print)
			throws IllegalArgumentException {
		int initialCharIndex = (int) (this.validateTransition(initialState, initialChar)[2]);
		String transition = this.getTransition(initialState, initialCharIndex, format);
		System.out.print(print ? (transition + '\n') : "");
		return transition;
	}

	public String getTransition(int initialState, String initialChar, boolean format) throws IllegalArgumentException {
		return this.getTransition(initialState, initialChar, format, false);
	}

	public String getTransition(int initialState, String initialChar) throws IllegalArgumentException {
		return this.getTransition(initialState, initialChar, false);
	}

	public String printTransition(int initialState, String initialChar, boolean format)
			throws IllegalArgumentException {
		return this.getTransition(initialState, initialChar, format, true);
	}

	public String printTransition(int initialState, String initialChar) throws IllegalArgumentException {
		return this.printTransition(initialState, initialChar, false);
	}

	public String[] getTransitions(int initialState, boolean format, boolean print) throws IllegalArgumentException {
		this.validateInitialState(initialState);
		String[] result = new String[this.getTapeAlphabetSize()];
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
		for (int i = 0; i < this.getAcceptState(); i++) {
			for (int j = 0; j < this.getTapeAlphabetSize(); j++) {
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

	public String getDefinedTransition(int initialState, String initialChar, boolean format, boolean print)
			throws IllegalArgumentException {
		int initialCharIndex = (int) (this.validateTransition(initialState, initialChar)[2]);
		String transition = (this.defined[initialState][initialCharIndex]
				? this.getTransition(initialState, initialCharIndex, format)
				: null);
		System.out.print(print ? (transition + '\n') : "");
		return transition;
	}

	public String getDefinedTransition(int initialState, String initialChar, boolean format)
			throws IllegalArgumentException {
		return this.getDefinedTransition(initialState, initialChar, format, false);
	}

	public String getDefinedTransition(int initialState, String initialChar) throws IllegalArgumentException {
		return this.getDefinedTransition(initialState, initialChar, false);
	}

	public String printDefinedTransition(int initialState, String initialChar, boolean format)
			throws IllegalArgumentException {
		return this.getDefinedTransition(initialState, initialChar, format, true);
	}

	public String printDefinedTransition(int initialState, String initialChar) throws IllegalArgumentException {
		return this.printDefinedTransition(initialState, initialChar, false);
	}

	public String[] getDefinedTransitions(int initialState, boolean format, boolean print)
			throws IllegalArgumentException {
		this.validateInitialState(initialState);
		int length = 0, t = this.getTapeAlphabetSize();
		String transition;
		String[] temp = new String[t];
		for (int i = 0; i < t; i++) {
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
		for (int i = 0; i < this.getAcceptState() && index < numDef; i++) {
			for (int j = 0; j < this.getTapeAlphabetSize() && index < numDef; j++) {
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

	public String getDefaultTransition(int initialState, String initialChar, boolean format, boolean print)
			throws IllegalArgumentException {
		this.validateTransition(initialState, initialChar);
		String transition = initialState + ' ' + initialChar + ' ' + initialState + ' ' + initialChar + ' '
				+ TMSS.RIGHT;
		if (format) {
			transition = "delta(" + initialState + ',' + initialChar + ") = (" + initialState + ',' + initialChar + ','
					+ TMSS.RIGHT + ')';
		}
		System.out.print(print ? (transition + '\n') : "");
		return transition;
	}

	public String getDefaultTransition(int initialState, String initialChar, boolean format)
			throws IllegalArgumentException {
		return this.getDefaultTransition(initialState, initialChar, format, false);
	}

	public String getDefaultTransition(int initialState, String initialChar) throws IllegalArgumentException {
		return this.getDefaultTransition(initialState, initialChar, false);
	}

	public String printDefaultTransition(int initialState, String initialChar, boolean format)
			throws IllegalArgumentException {
		return this.getDefaultTransition(initialState, initialChar, format, true);
	}

	public String printDefaultTransition(int initialState, String initialChar) throws IllegalArgumentException {
		return this.printDefaultTransition(initialState, initialChar, false);
	}

	public boolean isValidDirection(String direction) throws IllegalArgumentException {
		if (direction == null) {
			this.cause = "Given direction is null.";
			this.illegalArg();
		}

		for (String vd : this.validDirections) {
			if (vd.equals(direction)) {
				return true;
			}
		}
		return false;
	}

	public String validateDirection(String direction) throws IllegalArgumentException {
		if (!this.isValidDirection(direction)) {
			this.cause = "Given direction";
			if (this.isScanning) {
				this.cause += " on line " + this.lineNumber;
			}
			this.cause += '(' + direction + ") isn't a valid direction(one of ";
			StringBuilder s = new StringBuilder("");
			for (int i = 0; i < this.getNumValidDirections(); i++) {
				s.append(this.validDirections[i] + (i != this.getNumValidDirections() - 1 ? ", " : ""));
			}
			this.cause += s.toString() + ").";
			this.illegalArg();
		}
		return direction;
	}

	public int getNumValidDirections() {
		return this.validDirections.length;
	}

	public String[] getValidDirections() {
		String[] result = new String[this.getNumValidDirections()];
		System.arraycopy(this.validDirections, 0, result, 0, result.length);
		return result;
	}

	public boolean getIncludeStill() {
		return this.includeStill;
	}

	public String[] setIncludeStill(boolean includeStill) {
		if (this.includeStill = includeStill) {
			this.validDirections = (String[]) Arrays.asList(TMSS.LEFT, TMSS.RIGHT, TMSS.STILL).toArray();
		} else {
			this.validDirections = (String[]) Arrays.asList(TMSS.LEFT, TMSS.RIGHT).toArray();
		}

		String[] result = null;
		if (!this.getIncludeStill() && this.stillCount != 0) {
			result = new String[this.stillCount];
			int index = 0;
			for (int i = 0; i < this.getAcceptState() && this.stillCount != 0; i++) {
				for (int j = 0; j < this.getTapeAlphabetSize() && this.stillCount != 0; j++) {
					if (this.direction[i][j].equals(TMSS.STILL)) {
						result[index++] = this.resetTransition(i, j);
						this.defined[i][j] = false;
						this.numDefinedTransitions--;
						this.stillCount--;
					}
				}
			}
			this.strChange = true;
		}
		return result;
	}

	public static boolean isDefault(String s) {
		return TMSS.DEFAULT.equals(TMSS.lower(s));
	}

	public int getMaxStringCount() {
		return this.maxStringCount;
	}

	public static boolean isValidMaxStringCount(int maxStringCount) {
		return (maxStringCount >= 0);
	}

	public int validateMaxStringCount(int maxStringCount) throws IllegalArgumentException {
		if (!TMSS.isValidMaxStringCount(maxStringCount)) {
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
		if (this.getMaxStringCount() > TMSS.MAX_STRINGS_COUNT) {
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

			if (estimateStringCount > TMSS.MAX_STRINGS_COUNT) {
				this.cause = "There is approximately " + estimateStringCount
						+ " strings to test which is more than the maximum(" + TMSS.MAX_STRINGS_COUNT + ").";
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

	public int getInfiniteCount() {
		return this.infiniteCount;
	}

	public HashMap<ArrayList<Integer>, String> getResults() {
		return new HashMap<ArrayList<Integer>, String>(this.results);
	}

	public int getMinLength() {
		return this.minLength;
	}

	// even if it returns true, maxLength isn't necessarily valid since
	// initialLength hasn't been taken into account
	public static boolean isValidMinLength(int minLength) {
		return (minLength >= 0);
	}

	public int validateMinLength(int minLength) throws IllegalArgumentException {
		if (!TMSS.isValidMinLength(minLength)) {
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
		if (!TMSS.isValidMaxLength(maxLength)) {
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
			if (this.isConstructing && TMSS.isDefault(initialString)) {
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

	public long getMaxSteps() {
		return this.maxSteps;
	}

	public static boolean isValidMaxSteps(long maxSteps) {
		return (maxSteps >= 0);
	}

	public long validateMaxSteps(long maxSteps) throws IllegalArgumentException {
		if (!TMSS.isValidMaxSteps(maxSteps)) {
			this.cause = "Given max steps(" + maxSteps + ") is negative.";
			this.illegalArg();
		}
		return maxSteps;
	}

	public long setMaxSteps(long maxSteps) throws IllegalArgumentException {
		this.validateMaxSteps(maxSteps);
		this.strChange = this.strChange || (this.getMaxSteps() != maxSteps && this.getMaxStringCount() != 0);
		this.stepCount = 0;
		return (this.maxSteps = maxSteps);
	}

	public long getStepCount() {
		return this.stepCount;
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

	public boolean getTrace() {
		return this.trace;
	}

	public boolean setTrace(boolean trace) {
		this.strChange = this.strChange || (this.getTrace() != trace && this.getMaxStringCount() != 0);
		return (this.trace = trace);
	}

	public boolean getTimeLimit() {
		return this.timeLimit;
	}

	public boolean setTimeLimit(boolean timeLimit) {
		this.strChange = this.strChange || (this.getTimeLimit() != timeLimit && this.getMaxStringCount() != 0);
		return (this.timeLimit = timeLimit);
	}

	public long getMaxProcessTime() {
		return this.maxProcessTime;
	}

	public static boolean isValidMaxProcessTime(long maxProcessTime) {
		return (maxProcessTime >= TMSS.MIN_PROCESS_TIME && maxProcessTime <= TMSS.MAX_PROCESS_TIME);
	}

	public static String getMaxProcessTimeRange() {
		return ('[' + TMSS.MIN_PROCESS_TIME + ", " + TMSS.MAX_PROCESS_TIME + ']');
	}

	public long validateMaxProcessTime(long maxProcessTime) throws IllegalArgumentException {
		if (!TMSS.isValidMaxProcessTime(maxProcessTime)) {
			this.cause = "Given max process time(" + maxProcessTime + ") isn't in the range of "
					+ TMSS.getMaxProcessTimeRange() + '.';
			this.illegalArg();
		}
		return maxProcessTime;
	}

	public long setMaxProcessTime(long maxProcessTime) throws IllegalArgumentException {
		this.validateMaxProcessTime(maxProcessTime);
		this.strChange = this.strChange
				|| (this.getMaxProcessTime() != maxProcessTime && this.getTimeLimit() && this.getMaxStringCount() != 0);
		this.elapsedProcessTime = 0;
		this.nanoMaxProcessTime = maxProcessTime * TMSS.NANOSECONDS_PER_MILLISECOND;
		return (this.maxProcessTime = maxProcessTime);
	}

	public long getElapsedProcessTime() {
		return this.elapsedProcessTime;
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
		return TMSS.staticCause;
	}

	public String getTime() {
		return this.time;
	}

	public HashMap<String, String> getMachines() {
		return new HashMap<String, String>(this.machines);
	}

	public static int getMachineCount() {
		return TMSS.machineCount;
	}

	public boolean getOverwrote() {
		return this.overwrote;
	}

	public TMSS(int numStates, int tapeAlphabetSize, int inputAlphabetSize, String[] tapeAlphabet, boolean includeStill,
			int numTransitions, String[] transitions, int maxStringCount, int minLength, int maxLength, long maxSteps,
			String initialString, boolean trace, boolean timeLimit, long maxProcessTime, boolean includeComments,
			String comments) throws IllegalArgumentException {
		this.isConstructing = true;
		this.setNumStates(numStates);
		this.setAlphabet(tapeAlphabetSize, inputAlphabetSize, tapeAlphabet);
		this.setIncludeStill(includeStill);
		this.putTransitions(numTransitions, transitions);
		this.setMaxStringCount(maxStringCount);
		this.setRangeString(minLength, maxLength, initialString);
		this.setMaxSteps(maxSteps);
		this.setTrace(trace);
		this.setTimeLimit(timeLimit);
		this.setMaxProcessTime(maxProcessTime);
		this.setIncludeComments(includeComments);
		this.offerComments(comments);
		this.isConstructing = false;
		this.cause = TMSS.staticCause = null;
		TMSS.machineCount++;
	}

	public TMSS(int numStates, int tapeAlphabetSize, int inputAlphabetSize, String[] tapeAlphabet, boolean includeStill,
			int numTransitions, String[] transitions, int maxStringCount, int minLength, int maxLength, long maxSteps,
			String initialString, boolean trace, boolean timeLimit, long maxProcessTime, boolean includeComments)
			throws IllegalArgumentException {
		this(numStates, tapeAlphabetSize, inputAlphabetSize, tapeAlphabet, includeStill, numTransitions, transitions,
				maxStringCount, minLength, maxLength, maxSteps, initialString, trace, timeLimit, maxProcessTime,
				includeComments, null);
	}

	public TMSS(int numStates, int tapeAlphabetSize, int inputAlphabetSize, String[] tapeAlphabet, boolean includeStill,
			int numTransitions, String[] transitions, int maxStringCount, int minLength, int maxLength, long maxSteps,
			String initialString, boolean trace, boolean timeLimit, long maxProcessTime)
			throws IllegalArgumentException {
		this(numStates, tapeAlphabetSize, inputAlphabetSize, tapeAlphabet, includeStill, numTransitions, transitions,
				maxStringCount, minLength, maxLength, maxSteps, initialString, trace, timeLimit, maxProcessTime,
				TMSS.DEFAULT_INCLUDE_COMMENTS);
	}

	public TMSS(int numStates, int tapeAlphabetSize, int inputAlphabetSize, String[] tapeAlphabet, boolean includeStill,
			int numTransitions, String[] transitions, int maxStringCount, int minLength, int maxLength, long maxSteps,
			String initialString, boolean trace, boolean timeLimit) throws IllegalArgumentException {
		this(numStates, tapeAlphabetSize, inputAlphabetSize, tapeAlphabet, includeStill, numTransitions, transitions,
				maxStringCount, minLength, maxLength, maxSteps, initialString, trace, timeLimit,
				TMSS.DEFAULT_MAX_PROCESS_TIME);
	}

	public TMSS(int numStates, int tapeAlphabetSize, int inputAlphabetSize, String[] tapeAlphabet, boolean includeStill,
			int numTransitions, String[] transitions, int maxStringCount, int minLength, int maxLength, long maxSteps,
			String initialString, boolean trace) throws IllegalArgumentException {
		this(numStates, tapeAlphabetSize, inputAlphabetSize, tapeAlphabet, includeStill, numTransitions, transitions,
				maxStringCount, minLength, maxLength, maxSteps, initialString, trace, TMSS.DEFAULT_TIME_LIMIT);
	}

	public TMSS(int numStates, int tapeAlphabetSize, int inputAlphabetSize, String[] tapeAlphabet, boolean includeStill,
			int numTransitions, String[] transitions, int maxStringCount, int minLength, int maxLength, long maxSteps,
			String initialString) throws IllegalArgumentException {
		this(numStates, tapeAlphabetSize, inputAlphabetSize, tapeAlphabet, includeStill, numTransitions, transitions,
				maxStringCount, minLength, maxLength, maxSteps, initialString, TMSS.DEFAULT_TRACE);
	}

	public TMSS(int numStates, int tapeAlphabetSize, int inputAlphabetSize, String[] tapeAlphabet, boolean includeStill,
			int numTransitions, String[] transitions, int maxStringCount, int minLength, int maxLength, long maxSteps)
			throws IllegalArgumentException {
		this(numStates, tapeAlphabetSize, inputAlphabetSize, tapeAlphabet, includeStill, numTransitions, transitions,
				maxStringCount, minLength, maxLength, maxSteps, TMSS.DEFAULT_INITIAL_STRING);
	}

	public TMSS(int numStates, int tapeAlphabetSize, int inputAlphabetSize, String[] tapeAlphabet, boolean includeStill,
			int numTransitions, String[] transitions, int maxStringCount, int minLength, int maxLength)
			throws IllegalArgumentException {
		this(numStates, tapeAlphabetSize, inputAlphabetSize, tapeAlphabet, includeStill, numTransitions, transitions,
				maxStringCount, minLength, maxLength, TMSS.DEFAULT_MAX_STEPS);
	}

	public TMSS(int numStates, int tapeAlphabetSize, int inputAlphabetSize, String[] tapeAlphabet, boolean includeStill,
			int numTransitions, String[] transitions, int maxStringCount, int maxLength)
			throws IllegalArgumentException {
		this(numStates, tapeAlphabetSize, inputAlphabetSize, tapeAlphabet, includeStill, numTransitions, transitions,
				maxStringCount, TMSS.DEFAULT_MIN_LENGTH, maxLength);
	}

	public TMSS(int numStates, int tapeAlphabetSize, int inputAlphabetSize, String[] tapeAlphabet, boolean includeStill,
			int numTransitions, String[] transitions, int maxStringCount) throws IllegalArgumentException {
		this(numStates, tapeAlphabetSize, inputAlphabetSize, tapeAlphabet, includeStill, numTransitions, transitions,
				maxStringCount, TMSS.DEFAULT_MAX_LENGTH);
	}

	public TMSS(int numStates, int tapeAlphabetSize, int inputAlphabetSize, String[] tapeAlphabet, boolean includeStill,
			int numTransitions, String[] transitions) throws IllegalArgumentException {
		this(numStates, tapeAlphabetSize, inputAlphabetSize, tapeAlphabet, includeStill, numTransitions, transitions,
				TMSS.DEFAULT_MAX_STRING_COUNT);
	}

	public TMSS(int numStates, int tapeAlphabetSize, int inputAlphabetSize, String[] tapeAlphabet, boolean includeStill)
			throws IllegalArgumentException {
		this(numStates, tapeAlphabetSize, inputAlphabetSize, tapeAlphabet, includeStill, 0, new String[0]);
	}

	public TMSS(int numStates, int tapeAlphabetSize, int inputAlphabetSize, String[] tapeAlphabet)
			throws IllegalArgumentException {
		this(numStates, tapeAlphabetSize, inputAlphabetSize, tapeAlphabet, TMSS.DEFAULT_INCLUDE_STILL);
	}

	public TMSS(int tapeAlphabetSize, int inputAlphabetSize, String[] tapeAlphabet) throws IllegalArgumentException {
		this(TMSS.MIN_NUM_STATES, tapeAlphabetSize, inputAlphabetSize, tapeAlphabet);
	}

	// copy constructor
	public TMSS(TMSS other) throws NullPointerException {
		this(other.getNumStates(), other.getTapeAlphabetSize(), other.getInputAlphabetSize(),
				other.getTapeAlphabet(true), other.getIncludeStill(), other.getNumDefinedTransitions(),
				other.getDefinedTransitions(), other.getMaxStringCount(), other.getMinLength(), other.getMaxLength(),
				other.getMaxSteps(), other.getInitialString(), other.getTrace(), other.getTimeLimit(),
				other.getMaxProcessTime(), other.getIncludeComments(), other.getComments());
	}

	public TMSS getCopy() {
		return new TMSS(this);
	}

	// by creating a copy from calling the toString method,
	// the value of toString is saved for this instance as well
	public TMSS getStringCopy() {
		return new TMSS(this.toString());
	}

	// creates a turing machine by reading it (in YUTMFF) from in
	@SuppressWarnings("null")
	public TMSS(Scanner in) throws IllegalArgumentException {
		this.isScanning = this.isConstructing = true;

		if (in == null) {
			TMSS.staticCause = "Given scanner is null.";
			TMSS.illegalArg(TMSS.getStaticCause());
		}

		try {
			if (!in.hasNextLine()) {
				TMSS.staticCause = "Given machine description didn't have a first line.";
				TMSS.illegalArg(TMSS.getStaticCause());
			}
			// process first line
			String line = in.nextLine();
			this.lineNumber++;
			String[] s = line.split(TMSS.DELIMITER_STRING);
			if (s.length != TMSS.LINE_1_NUM_ENTRIES || TMSS.countDelimiters(line) != s.length - 1) {
				TMSS.staticCause = "Given first line(" + line + ") isn't valid.";
				TMSS.illegalArg(TMSS.getStaticCause());
			}

			int numStates = TMSS.MIN_NUM_STATES;
			try {
				numStates = Integer.parseInt(s[0]);
			} catch (NumberFormatException ex) {
				TMSS.staticCause = "Given number of states(" + s[0] + ") isn't a valid integer.";
				TMSS.illegalArg(TMSS.getStaticCause());
			}
			try {
				this.setNumStates(numStates);
			} catch (IllegalArgumentException ex) {
				TMSS.staticCause = this.getCause();
				this.illegalArg();
			}

			int inputAlphabetSize = TMSS.MIN_INPUT_ALPHABET_SIZE;
			try {
				inputAlphabetSize = Integer.parseInt(s[2]);
			} catch (NumberFormatException ex) {
				TMSS.staticCause = "Given input alphabet size(" + s[2] + ") isn't a valid integer.";
				TMSS.illegalArg(TMSS.getStaticCause());
			}

			int tapeAlphabetSize = inputAlphabetSize + TMSS.NUM_SPECIAL_TAPE_CHARS;
			try {
				tapeAlphabetSize = Integer.parseInt(s[1]);
			} catch (NumberFormatException ex) {
				TMSS.staticCause = "Given tape alphabet size(" + s[1] + ") isn't a valid integer.";
				TMSS.illegalArg(TMSS.getStaticCause());
			}

			if (!in.hasNextLine()) {
				TMSS.staticCause = "Given machine description didn't have a second line.";
				TMSS.illegalArg(TMSS.getStaticCause());
			}
			// process second line
			line = in.nextLine();
			this.lineNumber++;
			s = line.split(TMSS.DELIMITER_STRING);
			if (s.length != tapeAlphabetSize - TMSS.NUM_SPECIAL_TAPE_CHARS
					|| TMSS.countDelimiters(line) != s.length - 1) {
				TMSS.staticCause = "Given second line(" + line + ") isn't valid.";
				TMSS.illegalArg(TMSS.getStaticCause());
			}
			try {
				this.setAlphabet(tapeAlphabetSize, inputAlphabetSize, s);
			} catch (IllegalArgumentException ex) {
				TMSS.staticCause = this.getCause();
				this.illegalArg();
			}

			if (!in.hasNextLine()) {
				TMSS.staticCause = "Given machine description didn't have a third line.";
				TMSS.illegalArg(TMSS.getStaticCause());
			}
			// process third line
			line = in.nextLine();
			this.lineNumber++;
			s = line.split(TMSS.DELIMITER_STRING);
			if (s.length != TMSS.LINE_3_NUM_ENTRIES || TMSS.countDelimiters(line) != s.length - 1) {
				TMSS.staticCause = "Given third line(" + line + ") isn't valid.";
				TMSS.illegalArg(TMSS.getStaticCause());
			}

			int numTransitions = 0;
			try {
				if ((numTransitions = Integer.parseInt(s[0])) < 0) {
					TMSS.staticCause = "Given number of transitions(" + numTransitions + ") is negative.";
					TMSS.illegalArg(TMSS.getStaticCause());
				}
			} catch (NumberFormatException ex) {
				TMSS.staticCause = "Given number of transitions(" + s[0] + ") isn't a valid integer.";
				TMSS.illegalArg(TMSS.getStaticCause());
			}

			// process transition lines
			String[] transitions = new String[numTransitions];
			for (int i = 0; i < numTransitions; i++) {
				if (!in.hasNextLine()) {
					TMSS.staticCause = "Given machine description didn't have line " + (i + 4) + '.';
					TMSS.illegalArg(TMSS.getStaticCause());
				}
				transitions[i] = in.nextLine();
			}
			this.setIncludeStill(TMSS.DEFAULT_INCLUDE_STILL);
			try {
				this.putTransitions(numTransitions, transitions);
			} catch (IllegalArgumentException ex) {
				TMSS.staticCause = this.getCause();
				this.illegalArg();
			}

			int readMaxStringCount = TMSS.DEFAULT_MAX_STRING_COUNT, readMinLength = TMSS.DEFAULT_MIN_LENGTH,
					readMaxLength = TMSS.DEFAULT_MAX_LENGTH;
			long readMaxSteps = TMSS.DEFAULT_MAX_STEPS, readMaxProcessTime = TMSS.DEFAULT_MAX_PROCESS_TIME;
			String readInitialString = TMSS.DEFAULT_INITIAL_STRING;
			// process command line
			if (in.hasNextLine()) {
				line = in.nextLine();
				this.lineNumber++;
				if (!line.isEmpty()) {
					s = line.split(TMSS.DELIMITER_STRING);
					if (s.length > TMSS.COMMAND_LINE_MAX_NUM_ENTRIES || TMSS.countDelimiters(line) != s.length - 1) {
						TMSS.staticCause = "Given command line(" + line + ") isn't valid.";
						TMSS.illegalArg(TMSS.getStaticCause());
					}

					try {
						readMaxStringCount = Integer.parseInt(s[0]);
					} catch (NumberFormatException ex) {
						if (!TMSS.isDefault(s[0])) {
							TMSS.staticCause = "Given max string count(" + s[0] + ") isn't a valid integer.";
							TMSS.illegalArg(TMSS.getStaticCause());
						}
					}

					if (readMaxStringCount != 0) {
						if (s.length == 2) {
							try {
								readMaxLength = Integer.parseInt(s[1]);
							} catch (NumberFormatException ex) {
								if (!TMSS.isDefault(s[1])) {
									TMSS.staticCause = "Given max length(" + s[1] + ") isn't a valid integer.";
									TMSS.illegalArg(TMSS.getStaticCause());
								}
							}
						}

						if (s.length >= 3) {
							int first = TMSS.DEFAULT_MIN_LENGTH;
							int second = TMSS.DEFAULT_MAX_LENGTH;
							try {
								first = Integer.parseInt(s[1]);
							} catch (NumberFormatException ex) {
								if (!TMSS.isDefault(s[1])) {
									TMSS.staticCause = "Given first value for the string length bounds(" + s[1]
											+ ") isn't a valid integer.";
									TMSS.illegalArg(TMSS.getStaticCause());
								}
							}
							try {
								second = Integer.parseInt(s[2]);
							} catch (NumberFormatException ex) {
								if (!TMSS.isDefault(s[2])) {
									TMSS.staticCause = "Given second value for the string length bounds(" + s[2]
											+ ") isn't a valid integer.";
									TMSS.illegalArg(TMSS.getStaticCause());
								}
							}

							readMinLength = Math.min(first, second);
							readMaxLength = Math.max(first, second);
							for (int i = 0; i < readMinLength; i++) {
								readInitialString += this.inputAlphabet[0];
							}
						}

						if (s.length >= 4) {
							try {
								readMaxSteps = Long.parseLong(s[3]);
							} catch (NumberFormatException ex) {
								if (!TMSS.isDefault(s[3])) {
									TMSS.staticCause = "Given max steps(" + s[3] + ") isn't a valid integer.";
									TMSS.illegalArg(TMSS.getStaticCause());
								}
							}
						}

						readInitialString = s.length >= 5 ? s[4] : readInitialString;

						if (s.length >= 6) {
							if (!TMSS.isDefault(s[5])) {
								this.setTrace(TMSS.parseBoolean(s[5], "trace"));
							}
						}

						if (s.length >= 7) {
							if (!TMSS.isDefault(s[6])) {
								try {
									this.setTimeLimit(TMSS.parseBoolean(s[6], "time limit"));
								} catch (IllegalArgumentException ex) {
									if (s.length == 7) {
										try {
											this.validateMaxProcessTime(readMaxProcessTime = Long.parseLong(s[6]));
											this.setTimeLimit(true);
										} catch (NumberFormatException ex1) {
											TMSS.staticCause = "Given max process time(" + s[6]
													+ ") isn't a valid integer.";
											TMSS.illegalArg(TMSS.getStaticCause());
										} catch (IllegalArgumentException ex1) {
											TMSS.staticCause = this.getCause();
											this.illegalArg();
										}
									} else {
										TMSS.illegalArg(TMSS.getStaticCause());
									}
								}
							}
						}

						if (this.getTimeLimit() && s.length == 8) {
							try {
								readMaxProcessTime = Long.parseLong(s[7]);
							} catch (NumberFormatException ex) {
								if (!TMSS.isDefault(s[7])) {
									TMSS.staticCause = "Given max process time(" + s[7] + ") isn't a valid integer.";
									TMSS.illegalArg(TMSS.getStaticCause());
								}
							}
						}
					}
				}
			}
			try {
				this.setMaxStringCount(readMaxStringCount);
				this.setRangeString(readMinLength, readMaxLength, readInitialString);
				this.setMaxSteps(readMaxSteps);
				this.setMaxProcessTime(readMaxProcessTime);
			} catch (IllegalArgumentException ex) {
				TMSS.staticCause = this.getCause();
				this.illegalArg();
			}

			// process comments
			this.setIncludeComments(TMSS.DEFAULT_INCLUDE_COMMENTS);
			StringBuilder comments = new StringBuilder("");
			while (in.hasNextLine()) {
				comments.append(in.nextLine() + '\n');
				this.lineNumber++;
			}
			in.close(); // close upon success
			// trim last extra '\n' from comments
			this.offerComments(comments.subSequence(0, comments.length() - 1));

			this.isScanning = this.isConstructing = false;
			this.cause = TMSS.staticCause = null;
			TMSS.machineCount++;
		} catch (IllegalArgumentException ex) {
			in.close(); // close upon failure to avoid resource leak
			ex.printStackTrace();
			throw new IllegalArgumentException(ex.getMessage());
		} catch (IllegalStateException ex) {
			// no need to close scanner since it's already closed
			ex.printStackTrace();
			TMSS.staticCause = "Given scanner is closed.";
			TMSS.illegalArg(TMSS.getStaticCause());
		}
	}

	@SuppressWarnings("resource")
	public TMSS(File f) throws IllegalArgumentException, NullPointerException, FileNotFoundException {
		this(new Scanner(f));
	}

	@SuppressWarnings("resource")
	public TMSS(String s, boolean isPathName)
			throws IllegalArgumentException, NullPointerException, FileNotFoundException {
		this(isPathName ? new Scanner(new File(s)) : new Scanner(s));
	}

	@SuppressWarnings("resource")
	public TMSS(CharSequence c) throws IllegalArgumentException, NullPointerException {
		this(new Scanner(c.toString()));
	}

	@SuppressWarnings("resource")
	public TMSS(InputStream s) throws IllegalArgumentException, NullPointerException {
		this(new Scanner(s));
	}

	public TMSS() throws IllegalArgumentException {
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
				this.putTransition((int) result[0], (String) result[1], (int) result[2], (String) result[3],
						(String) result[4], replace[i]);
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

	public String putTransition(int initialState, String initialChar, int finalState, String finalChar,
			String direction, boolean replace) throws IllegalArgumentException {
		Object[] result = this.validateTransition(initialState, initialChar, finalState, finalChar, direction);
		int initialCharIndex = (int) result[5], finalCharIndex = (int) result[6];
		String transition = (String) result[7];
		if (!replace && this.defined[initialState][initialCharIndex]) {
			this.cause = "Given transition";
			if (this.isScanning) {
				this.cause += " on line " + this.lineNumber;
			}
			this.cause += '(' + transition + ") has the same initial state and initial character"
					+ " as another transition defined before it.";
			this.illegalArg();
		}

		this.nextState[initialState][initialCharIndex] = finalState;
		this.charToWriteIndex[initialState][initialCharIndex] = finalCharIndex;
		if (!this.defined[initialState][initialCharIndex]) {
			this.defined[initialState][initialCharIndex] = true;
			this.numDefinedTransitions++;
			this.stateNumDefined[initialState]++;
			this.stillCount += direction.equals(TMSS.STILL) ? 1 : 0;
		} else {
			String curDir = this.direction[initialState][initialCharIndex];
			if (!curDir.equals(TMSS.STILL) && direction.equals(TMSS.STILL)) {
				this.stillCount++; // gain a STILL direction
			} else if (curDir.equals(TMSS.STILL) && !direction.equals(TMSS.STILL)) {
				this.stillCount--; // lose a STILL direction
			}
		}
		this.direction[initialState][initialCharIndex] = direction;
		this.strChange = true;
		return transition;
	}

	public String putTransition(int initialState, String initialChar, int finalState, String finalChar,
			String direction) throws IllegalArgumentException {
		return this.putTransition(initialState, initialChar, finalState, finalChar, direction, false);
	}

	public boolean isValidTransition(String transition) {
		try {
			Object[] result = this.validateTransition(transition);
			return this.isValidTransition((int) result[0], (String) result[1], (int) result[2], (String) result[3],
					(String) result[4]);
		} catch (IllegalArgumentException ex) {
			return false;
		}
	}

	public boolean isValidTransition(int initialState, String initialChar, int finalState, String finalChar,
			String direction) {
		try { // if no exception is thrown then the result is necessarily true
			return (this.validateTransition(initialState, initialChar, finalState, finalChar, direction) != null);
		} catch (IllegalArgumentException ex) {
			return false;
		}
	}

	public boolean isValidDefinedTransition(String transition) throws IllegalArgumentException {
		Object[] result = this.validateTransition(transition);
		return this.isValidDefinedTransition((int) result[0], (String) result[1], (int) result[2], (String) result[3],
				(String) result[4]);
	}

	public boolean isValidDefinedTransition(int initialState, String initialChar, int finalState, String finalChar,
			String direction) throws IllegalArgumentException {
		int initialCharIndex = (int) (this.validateTransition(initialState, initialChar, finalState, finalChar,
				direction)[5]);
		return this.defined[initialState][initialCharIndex];
	}

	@SuppressWarnings("null")
	public Object[] validateTransition(String transition) throws IllegalArgumentException {
		if (transition == null) {
			this.cause = "Given transition is null.";
			this.illegalArg();
		}

		String[] s = transition.split(TMSS.DELIMITER_STRING);
		if (s.length != 5 || TMSS.countDelimiters(transition) != s.length - 1) {
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

		Object[] result = { initialState, s[1], finalState, s[3], s[4] };
		return result;
	}

	public Object[] validateTransition(int initialState, String initialChar, int finalState, String finalChar,
			String direction) throws IllegalArgumentException {
		int initialCharIndex = (int) (this.validateTransition(initialState, initialChar)[2]);
		int finalCharIndex = this.validateTapeChar(finalChar, false);
		String transition = initialState + ' ' + initialChar + ' ' + finalState + ' ' + finalChar + ' ' + direction;
		Object[] result = { initialState, initialChar, this.validateFinalState(finalState), finalChar,
				this.validateDirection(direction), initialCharIndex, finalCharIndex, transition };
		return result;
	}

	public Object[] validateTransition(int initialState, String initialChar) throws IllegalArgumentException {
		Object[] result = { this.validateInitialState(initialState), initialChar, this.validateTapeChar(initialChar) };
		return result;
	}

	private String resetTransition(int initialState, int initialCharIndex) {
		String transition = this.getTransition(initialState, initialCharIndex, false);
		// set default values
		this.nextState[initialState][initialCharIndex] = initialState;
		this.charToWriteIndex[initialState][initialCharIndex] = initialCharIndex;
		this.direction[initialState][initialCharIndex] = TMSS.RIGHT;
		return transition;
	}

	private void finalizeReset(int initialState, int initialCharIndex, String direction) {
		this.defined[initialState][initialCharIndex] = false;
		this.numDefinedTransitions--;
		this.stateNumDefined[initialState]--;
		this.stillCount += direction.equals(TMSS.STILL) ? -1 : 0;
		this.strChange = true;
	}

	public String resetTransition(int initialState, String initialChar) throws IllegalArgumentException {
		int initialCharIndex = (int) (this.validateTransition(initialState, initialChar)[2]);
		String direction = this.direction[initialState][initialCharIndex];
		String transition = this.resetTransition(initialState, initialCharIndex);
		if (this.defined[initialState][initialCharIndex]) {
			this.finalizeReset(initialState, initialCharIndex, direction);
		}
		return transition;
	}

	public String[] resetTransitions(int initialState) throws IllegalArgumentException {
		this.validateInitialState(initialState);
		String[] result = new String[this.getTapeAlphabetSize()];
		for (int i = 0; i < result.length; i++) {
			String direction = this.direction[initialState][i];
			result[i] = this.resetTransition(initialState, i);
			if (this.defined[initialState][i]) {
				this.finalizeReset(initialState, i, direction);
			}
		}
		return result;
	}

	public String[] resetTransitions() {
		String[] result = new String[this.getTotalNumTransitions()];
		int index = 0;
		for (int i = 0; i < this.getAcceptState(); i++) {
			this.stateNumDefined[i] = 0;
			for (int j = 0; j < this.getTapeAlphabetSize(); j++) {
				result[index++] = this.resetTransition(i, j);
				this.defined[i][j] = false;
			}
		}
		if (this.getNumDefinedTransitions() != 0) {
			this.numDefinedTransitions = 0;
			this.stillCount = 0;
			this.strChange = true;
		}
		return result;
	}

	public String resetDefinedTransition(int initialState, String initialChar) throws IllegalArgumentException {
		int initialCharIndex = (int) (this.validateTransition(initialState, initialChar)[2]);
		String transition = null;
		if (this.defined[initialState][initialCharIndex]) {
			String direction = this.direction[initialState][initialCharIndex];
			transition = this.resetTransition(initialState, initialCharIndex);
			this.finalizeReset(initialState, initialCharIndex, direction);
		}
		return transition;
	}

	public String[] resetDefinedTransitions(int initialState) throws IllegalArgumentException {
		this.validateInitialState(initialState);
		int length = 0, t = this.getTapeAlphabetSize();
		String transition;
		String[] temp = new String[t];
		for (int i = 0; i < t && this.stateNumDefined[initialState] != 0; i++) {
			transition = null;
			if (this.defined[initialState][i]) {
				String direction = this.direction[initialState][i];
				transition = this.resetTransition(initialState, i);
				this.finalizeReset(initialState, i, direction);
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
		for (int i = 0; i < this.getAcceptState() && this.getNumDefinedTransitions() != 0; i++) {
			for (int j = 0; j < this.getTapeAlphabetSize() && this.getNumDefinedTransitions() != 0; j++) {
				if (this.defined[i][j]) {
					String direction = this.direction[i][j];
					result[index++] = this.resetTransition(i, j);
					this.finalizeReset(i, j, direction);
				}
			}
		}
		return result;
	}

	private void initializeTransitions() {
		int a = this.getAcceptState(), t = this.getTapeAlphabetSize();
		this.nextState = new int[a][t];
		this.charToWriteIndex = new int[a][t];
		this.direction = new String[a][t];
		this.defined = new boolean[a][t];
		this.numDefinedTransitions = 0;
		for (int i = 0; i < a; i++) {
			for (int j = 0; j < t; j++) {
				// set default values
				this.nextState[i][j] = i;
				this.charToWriteIndex[i][j] = j;
				this.direction[i][j] = TMSS.RIGHT;
			}
		}
		this.strChange = true;
	}

	@SuppressWarnings("null")
	public static int countDelimiters(String s) throws IllegalArgumentException {
		if (s == null) {
			TMSS.staticCause = "Given string is null.";
			TMSS.illegalArg(TMSS.getStaticCause());
		}

		int count = 0;
		for (int i = 0; i < s.length(); i++) {
			count += s.charAt(i) == TMSS.DELIMITER_CHAR ? 1 : 0;
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
			return (TMSS.parseBoolean(s) || true);
		} catch (IllegalArgumentException ex) {
			return false;
		}
	}

	private static boolean parseBoolean(String s, String name) throws IllegalArgumentException {
		if (s == null) {
			TMSS.staticCause = "Given string is null.";
			TMSS.illegalArg(TMSS.getStaticCause());
		}

		String check = TMSS.lower(s);
		if (check != null) {
			if (check.equals(TMSS.TRUE_1) || check.equals(TMSS.TRUE_2)) {
				return true;
			} else if (check.equals(TMSS.FALSE_1) || check.equals(TMSS.FALSE_2)) {
				return false;
			}
		}

		TMSS.staticCause = "Given " + name + '(' + s + ") doesn't represent a valid boolean.";
		TMSS.illegalArg(TMSS.getStaticCause());
		return false;
	}

	public static boolean parseBoolean(String s) throws IllegalArgumentException {
		return TMSS.parseBoolean(s, "string");
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
							"Testing the first " + TMSS.comma(this.getMaxStringCount()) + " strings starting from ");
				}
				message = this.toString(testString, true).toLowerCase();
				System.out.println(message + '.');
				if (this.getMaxStringCount() != 1 || !this.getTrace()) {
					System.out.print('\n');
				}
			}
		}

		this.acceptCount = this.rejectCount = this.infiniteCount = 0;
		// maps testString to output:stepCount:elapsedProcessTime
		this.results = new HashMap<ArrayList<Integer>, String>(this.getMaxStringCount());

		long beforeTime = System.nanoTime();
		int count = 0;
		while (testString.size() <= this.getMaxLength() && ++count <= this.getMaxStringCount()) {
			int output = this.run(testString, count, print);
			value = output + ":" + this.getStepCount()
					+ (this.getTimeLimit() ? ":" + this.getElapsedProcessTime() : "");
			this.results.put(testString, value);

			if (print && !this.getTrace()) {
				message = this.toString(testString, true);
				if (output == 1) {
					message += " was accepted after " + this.comma() + this.getSteps()
							+ (this.getTimeLimit() ? " in " + this.formatTime() : "") + '.';
				} else if (output == 0) {
					message += " was rejected after " + this.comma() + this.getSteps()
							+ (this.getTimeLimit() ? " in " + this.formatTime() : "") + '.';
				} else if (output == -1) {
					message += " didn't terminate within " + this.comma() + this.getSteps()
							+ (this.getTimeLimit() ? " in " + this.formatTime() : "") + '.';
				} else { // output == -2
					message += " didn't terminate within " + this.comma() + this.getSteps()
							+ (this.getTimeLimit() ? " in " + this.formatTime() : "") + '.';
				}
				System.out.println(message);
			}

			this.incrementTestString(testString);
		}
		long elapsedTime = TMSS.nano2Milli(System.nanoTime() - beforeTime);
		this.time = TMSS.formatTime(elapsedTime);

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
		return (this.getAcceptCount() + ":" + this.getRejectCount() + ":" + this.getInfiniteCount());
	}

	public String simulate() {
		return this.simulate(true);
	}

	private int run(ArrayList<Integer> testString, int count, boolean print) {
		if (print && this.getTrace() && count != 1) {
			System.out.print('\n');
		}

		int initialState = 0, initialHeadPos = 1;
		int output = this.run(testString, initialState, initialHeadPos, print);
		if (this.count) {
			if (output == 1) {
				this.acceptCount++;
			} else if (output == 0) {
				this.rejectCount++;
			} else { // output == -1 || output == -2
				this.infiniteCount++;
			}
		}
		return output;
	}

	public int run(ArrayList<Integer> testString, int state, int headPos, boolean print)
			throws IllegalArgumentException {
		ArrayList<Integer> tape = this.testStringToTape(testString);
		if (!this.isSimulating) {
			this.validateInitialState(state);
			this.validateHeadPos(tape, headPos);
		}

		String s = this.toString(testString, true).toLowerCase();
		if (print && this.getTrace()) {
			if (this.count) {
				System.out.println("Starting to test " + s + '.');
			}
			this.printConfig(tape, state, headPos);
		}

		this.stepCount = this.elapsedProcessTime = 0;
		long beforeTime;
		// run the machine for maxSteps steps
		while (state < this.getAcceptState() && ++this.stepCount <= this.getMaxSteps()) {
			beforeTime = this.getTimeLimit() ? System.nanoTime() : 0;

			if (headPos == tape.size()) {
				// extend tape if machine has run beyond right end
				this.extendTape(tape, false);
			} else if (headPos == -1) {
				// extend tape if machine has run beyond left end
				this.extendTape(tape, true);
				headPos++;
			}

			// simulate one step of the machine
			int oldCharIndex = tape.get(headPos);
			tape.set(headPos, this.charToWriteIndex[state][oldCharIndex]);
			String direction = this.direction[state][oldCharIndex];
			if (!this.getIncludeStill() || !direction.equals(TMSS.STILL)) {
				headPos += direction.equals(TMSS.LEFT) ? -1 : 1;
			}
			state = this.nextState[state][oldCharIndex];

			// keep track of process time
			if (this.getTimeLimit()) {
				this.elapsedProcessTime += System.nanoTime() - beforeTime;
				if (this.getElapsedProcessTime() > this.nanoMaxProcessTime) {
					this.elapsedProcessTime = TMSS.nano2Milli(this.getElapsedProcessTime());
					if (print && this.getTrace()) {
						System.out.println("Turing machine ran for " + TMSS.comma(--this.stepCount) + this.getSteps()
								+ " on " + s + " without halting in " + this.formatTime() + '.');
					}
					return -2;
				}
			}

			if (this.getTrace()) {
				this.printConfig(tape, state, headPos);
			}
		}
		this.elapsedProcessTime = this.getTimeLimit() ? TMSS.nano2Milli(this.getElapsedProcessTime()) : 0;

		if (state == this.getAcceptState()) {
			if (print && this.getTrace()) {
				System.out.println("Turing machine has accepted " + s + " after " + this.comma() + this.getSteps()
						+ (this.getTimeLimit() ? " in " + this.formatTime() : "") + '.');
			}
			return 1;
		} else if (state == this.getRejectState()) {
			if (print && this.getTrace()) {
				System.out.println("Turing machine has rejected " + s + " after " + this.comma() + this.getSteps()
						+ (this.getTimeLimit() ? " in " + this.formatTime() : "") + '.');
			}
			return 0;
		} else {
			if (print && this.getTrace()) {
				System.out.println("Turing machine ran for " + TMSS.comma(--this.stepCount) + this.getSteps() + " on "
						+ s + " without halting" + (this.getTimeLimit() ? " in " + this.formatTime() : "") + '.');
			}
			return -1;
		}
	}

	public ArrayList<Integer> testStringToTape(ArrayList<Integer> testString) throws IllegalArgumentException {
		if (!this.isSimulating) {
			this.validateTestString(testString);
		}

		return new ArrayList<Integer>(testString);
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

	public boolean isValidTape(ArrayList<Integer> tape) {
		try { // if no exception is thrown then the result is necessarily true
			return (this.validateTape(tape) != null);
		} catch (IllegalArgumentException ex) {
			return false;
		}
	}

	@SuppressWarnings("null")
	public ArrayList<Integer> validateTape(ArrayList<Integer> tape) throws IllegalArgumentException {
		if (tape == null) {
			this.cause = "Given turing machine tape is null.";
			this.illegalArg();
		}

		for (int i = 0; i < tape.size(); i++) {
			if (!this.isValidTapeCharIndex(i)) {
				this.cause = "Character index " + (i + 1)
						+ " on the given turing machine tape isn't valid(not in the range of "
						+ this.getTapeCharIndexRange() + ").";
				this.illegalArg();
			}
		}

		return tape;
	}

	public ArrayList<Integer> validateHeadPos(ArrayList<Integer> tape, int headPos) throws IllegalArgumentException {
		if (!this.isSimulating) {
			this.validateTape(tape);
		}
		if (headPos < 0) {
			while (headPos++ != 0) {
				this.extendTape(tape, true);
			}
		}
		if (headPos > tape.size() - 1) {
			while (headPos != tape.size() - 1) {
				this.extendTape(tape, false);
			}
		}
		return tape;
	}

	private ArrayList<Integer> extendTape(ArrayList<Integer> tape, boolean left) {
		tape.add((left ? 0 : tape.size()), this.getBlankIndex());
		return tape;
	}

	public void printMachine() {
		System.out.print("\nTape alphabet:");
		for (int i = 0; i < this.getTapeAlphabetSize(); i++) {
			System.out.print(' ' + this.tapeAlphabet[i]);
		}

		System.out.print("\nInput alphabet:");
		for (int i = 0; i < this.getInputAlphabetSize(); i++) {
			System.out.print(' ' + this.inputAlphabet[i]);
		}

		System.out.println("\n\nNumber of defined transitions: " + this.getNumDefinedTransitions());
		System.out.println("Transition table:");
		this.printTransitions(true);
	}

	// prints a configuration of the machine
	public ArrayList<Integer> printConfig(ArrayList<Integer> tape, int state, int headPos)
			throws IllegalArgumentException {
		if (!this.isSimulating) {
			this.validateFinalState(state);
			this.validateHeadPos(tape, headPos);
			System.out.print("Tape configuration: ");
		} else {
			System.out.print("Configuration after " + this.comma() + this.getSteps() + ": ");
		}

		for (int i = 0; i < tape.size(); i++) {
			if (headPos == i) {
				System.out.print('q' + state + ' ');
			}
			System.out.print(this.tapeAlphabet[tape.get(i)]);
			if (i != tape.size() - 1) {
				System.out.print(' ');
			}
		}

		if (headPos == tape.size()) {
			System.out.print(" q" + state);
		}
		System.out.print('\n');

		return tape;
	}

	public String printSimulationInfo() {
		if (this.count) {
			System.out.print('\n');
			if (this.getActualStringCount() == 1) {
				System.out.println("There was only 1 string to test.");
			} else {
				if (this.getMaxStringCount() != this.getActualStringCount()) {
					System.out.println(
							"There were only " + TMSS.comma(this.getActualStringCount()) + " strings to test.");
				}

				if (this.getAcceptCount() == this.getActualStringCount()) {
					System.out.println("All of the tested strings were accepted.");
				} else if (this.getRejectCount() == this.getActualStringCount()) {
					System.out.println("All of the tested strings were rejected.");
				} else if (this.getInfiniteCount() == this.getActualStringCount()) {
					System.out.println("None of the tested strings terminated within " + TMSS.comma(this.getMaxSteps())
							+ TMSS.getSteps(this.getMaxSteps()) + '.');
				} else {
					if (this.getAcceptCount() != 0) {
						if (this.getAcceptCount() == 1) {
							System.out.println("1 string was accepted.");
						} else {
							System.out.println(TMSS.comma(this.getAcceptCount()) + " strings were accepted.");
						}
					}

					if (this.getRejectCount() != 0) {
						if (this.getRejectCount() == 1) {
							System.out.println("1 string was rejected.");
						} else {
							System.out.println(TMSS.comma(this.getRejectCount()) + " strings were rejected.");
						}
					}

					if (this.getInfiniteCount() != 0) {
						if (this.getInfiniteCount() == 1) {
							System.out.println("1 string didn't terminate within " + TMSS.comma(this.getMaxSteps())
									+ TMSS.getSteps(this.getMaxSteps()) + '.');
						} else {
							System.out.println(TMSS.comma(this.getInfiniteCount()) + " strings didn't terminate within "
									+ TMSS.comma(this.getMaxSteps()) + TMSS.getSteps(this.getMaxSteps()) + '.');
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
		TMSS.illegalArg(this.getCause());
	}

	// recursively add a ',' after every 3 characters of s starting from the right
	public static String comma(String s) throws NullPointerException {
		if (s.length() <= 3) {
			return s;
		}
		return TMSS.comma(s.substring(0, s.length() - 3)) + ',' + s.substring(s.length() - 3);
	}

	public static String comma(long l) {
		return TMSS.comma(Long.toString(l));
	}

	public String comma() {
		return TMSS.comma(this.getStepCount());
	}

	private static String getSteps(long step) {
		return (step == 1 ? " step" : " steps");
	}

	private String getSteps() {
		return TMSS.getSteps(this.getStepCount());
	}

	public static String formatTime(long time, boolean shortForm) {
		if (time < 0) {
			TMSS.staticCause = "Given value of time(" + time + ") is negative.";
			TMSS.illegalArg(TMSS.getStaticCause());
		} else if (time == 0) {
			return "nearly 0 milliseconds";
		}

		int millis = (int) (time % TMSS.MILLISECONDS_PER_SECOND);
		Long seconds = (long) 0;
		Integer minutes = 0, hours = 0, days = 0, weeks = 0, months = 0;

		if (time >= TMSS.MILLISECONDS_PER_SECOND) {
			seconds = time / TMSS.MILLISECONDS_PER_SECOND;
			TMSS.timeCalculate(seconds, TMSS.SECONDS_PER_MONTH, months);
			TMSS.timeCalculate(seconds, TMSS.SECONDS_PER_WEEK, weeks);
			TMSS.timeCalculate(seconds, TMSS.SECONDS_PER_DAY, days);
			TMSS.timeCalculate(seconds, TMSS.SECONDS_PER_HOUR, hours);
			TMSS.timeCalculate(seconds, TMSS.SECONDS_PER_MINUTE, minutes);
		}

		final String[] MS = { "millisecond", "ms" }, S = { "second", "s" }, M = { "minute", "mins" },
				H = { "hour", "h" };
		final int index = shortForm ? 1 : 0;

		StringBuilder s = new StringBuilder("");
		TMSS.timeAppend(s, months, "month");
		TMSS.timeAppend(s, weeks, "week");
		TMSS.timeAppend(s, days, "day");
		TMSS.timeAppend(s, hours, H[index], shortForm);
		TMSS.timeAppend(s, minutes, M[index], shortForm);
		TMSS.timeAppend(s, TMSS.safeCastLong2Int(seconds), S[index], shortForm);
		TMSS.timeAppend(s, millis, MS[index], shortForm);
		String output = s.toString();
		output = output.replaceAll("(and)", " ");
		return output.trim().replaceAll("( )+", "and");
	}

	public static String formatTime(long time) {
		return TMSS.formatTime(time, false);
	}

	public String formatTime() {
		return TMSS.formatTime(this.getElapsedProcessTime(), true);
	}

	@SuppressWarnings("unused")
	private static void timeCalculate(Long seconds, int bound, Integer remainder) {
		if (seconds >= bound) {
			remainder = (int) (seconds / bound);
			seconds %= bound;
		}
	}

	private static void timeAppend(StringBuilder s, int val, String unit, boolean shortForm) {
		if (val == 1) {
			s.append("1 " + unit);
		} else if (val != 0) {
			s.append(val + ' ' + unit);
			s.append(!shortForm ? 's' : "");
		}
		s.append(s.length() != 0 ? " and " : "");
	}

	private static void timeAppend(StringBuilder s, int val, String unit) {
		TMSS.timeAppend(s, val, unit, false);
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
			TMSS.staticCause = "Given time in nanoseconds(" + nanoSeconds + ") is negative.";
			TMSS.illegalArg(TMSS.getStaticCause());
		}
		return Math.round((double) nanoSeconds / TMSS.NANOSECONDS_PER_MILLISECOND);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		} else if (!(obj instanceof TMSS)) {
			return false;
		}
		TMSS other = (TMSS) obj;

		if (this.getNumStates() != other.getNumStates()) {
			return false;
		} else if (this.getTapeAlphabetSize() != other.getTapeAlphabetSize()) {
			return false;
		} else if (this.getInputAlphabetSize() != other.getInputAlphabetSize()) {
			return false;
		} else if (!this.tapeIndex.equals(other.tapeIndex)) {
			return false;
		}

		for (int i = 0; i < this.getAcceptState(); i++) {
			for (int j = 0; j < this.getTapeAlphabetSize(); j++) {
				if (this.nextState[i][j] != other.nextState[i][j]) {
					return false;
				} else if (this.charToWriteIndex[i][j] != other.charToWriteIndex[i][j]) {
					return false;
				} else if (!this.direction[i][j].equals(other.direction[i][j])) {
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
		result = prime * result + Arrays.deepHashCode(this.charToWriteIndex);
		result = prime * result + Arrays.deepHashCode(this.defined);
		result = prime * result + Arrays.hashCode(this.inputAlphabet);
		result = prime * result + this.getInputAlphabetSize();
		result = prime * result + this.inputIndex.hashCode();
		result = prime * result + Arrays.deepHashCode(this.direction);
		result = prime * result + Arrays.deepHashCode(this.nextState);
		result = prime * result + this.getNumDefinedTransitions();
		result = prime * result + this.getNumStates();
		result = prime * result + Arrays.hashCode(this.tapeAlphabet);
		result = prime * result + this.getTapeAlphabetSize();
		result = prime * result + this.tapeIndex.hashCode();
		result = prime * result + this.getTotalNumTransitions();
		return result;
	}

	@Override
	public String toString() {
		if (!this.strChange) {
			return this.savedStr;
		}
		StringBuilder output = new StringBuilder("");

		// first line
		output.append(
				this.getNumStates() + ' ' + this.getTapeAlphabetSize() + ' ' + this.getInputAlphabetSize() + '\n');

		// second line
		for (int i = 0; i < this.getBlankIndex(); i++) {
			output.append(this.tapeAlphabet[i]);
			output.append(i != this.getBlankIndex() - 1 ? ' ' : "");
		}

		// third line
		output.append('\n' + this.getNumDefinedTransitions() + '\n');

		// transition lines
		String[] definedTransitions = this.getDefinedTransitions();
		for (int i = 0; i < definedTransitions.length; i++) {
			output.append(definedTransitions[i] + '\n');
		}

		// command line
		if (this.getMaxStringCount() == 0) {
			output.append('0');
		} else {
			StringBuilder command = new StringBuilder("");
			command.append((this.getMaxStringCount() == TMSS.DEFAULT_MAX_STRING_COUNT ? TMSS.DEFAULT
					: this.getMaxStringCount()) + " ");
			command.append((this.getMinLength() == TMSS.DEFAULT_MIN_LENGTH ? TMSS.DEFAULT : this.getMinLength()) + " ");
			command.append((this.getMaxLength() == TMSS.DEFAULT_MAX_LENGTH ? TMSS.DEFAULT : this.getMaxLength()) + " ");
			command.append((this.getMaxSteps() == TMSS.DEFAULT_MAX_STEPS ? TMSS.DEFAULT : this.getMaxSteps()) + " ");
			command.append((this.getInitialLength() == 0 ? TMSS.DEFAULT : this.getInitialString()) + ' ');
			command.append(!this.getTrace() ? TMSS.DEFAULT : TMSS.TRUE_2);
			if (this.getTimeLimit()) {
				if (this.getMaxProcessTime() != TMSS.DEFAULT_MAX_PROCESS_TIME) {
					command.append(' ' + this.getMaxProcessTime());
				} else {
					command.append(" true");
				}
				output.append(command);
			} else {
				output.append(this.commandLine(command.toString()));
			}
		}

		// comments
		output.append("\n" + (this.getIncludeComments() ? this.comments : ""));

		this.strChange = false;
		return (this.savedStr = output.toString());
	}

	private String commandLine(String command) {
		while (command.endsWith(TMSS.DEFAULT)) {
			int index = command.lastIndexOf(TMSS.DEFAULT);
			// remove last occurrence of | default| or just |default|
			command = index != 0 ? command.substring(0, index - 1) : "";
		}
		if (!command.isEmpty()) {
			String[] s = command.split(TMSS.DELIMITER_STRING);
			if (s.length == 5 && this.getInitialLength() == this.getMinLength()
					&& this.isMinTestString(this.initialArray)) {
				// special case where the initialString is the minimum
				// possible String with length in the range
				// [minLength, maxLength]: the initialString(s[4])
				// can be removed since we can accomplish the same
				// effect by having nothing there
				command = s[0] + ' ' + s[1] + ' ' + s[2] + ' ' + s[3];
			} else if (s.length == 3 && this.getMinLength() == TMSS.DEFAULT_MIN_LENGTH) {
				// special case where the minLength is its default value
				// and the command line is: |maxStringCount minLength maxLength|
				// minLength(s[1]) can be removed since we can accomplish
				// the same effect by just putting maxLength
				command = s[0] + ' ' + s[2];
			} else if (s.length == 2) {
				// special case where the maxLength has been removed but
				// the minLength hasn't. To avoid having the constructor
				// interpret the minLength as the maxLength, we have to
				// append a TMSS.DEFAULT
				command += ' ' + TMSS.DEFAULT;
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
		if (!TMSS.isValidFileName(fileName)) {
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
		return this.saveToFile(TMSS.DEFAULT_FILE_NAME, overwrite);
	}

	public String saveToFile() throws IllegalArgumentException, IOException {
		return this.saveToFile(TMSS.DEFAULT_FILE_NAME, false);
	}

	@SuppressWarnings("null")
	public static TMSS main(TMSS m, String[] args, boolean stdin) throws IllegalArgumentException {
		TMSS machine = m;
		int eval = 0;
		boolean success = machine != null, save = false;
		String s = null;

		if (args != null) {
			for (int i = 0; i < args.length; i++) {
				if (args[i] == null || args[i].isEmpty()) {
					continue;
				}

				if ((s = TMSS.lower(args[i])) != null) {
					save = save || s.equals(TMSS.SAVE);
					stdin = stdin || s.equals(TMSS.STDIN);
					if (s.equals(TMSS.TRUE_1) || s.equals(TMSS.TRUE_2)) {
						eval++;
					} else if (s.equals(TMSS.FALSE_1) || s.equals(TMSS.FALSE_2)) {
						eval--;
					}
				}

				if (!success && !stdin) {
					try { // if no exception is thrown then the result is necessarily true
						success = (machine = new TMSS(args[i], true)) != null;
					} catch (FileNotFoundException ex) {
						try { // if no exception is thrown then the result is necessarily true
							success = (machine = new TMSS((args[i] + ".txt"), true)) != null;
						} catch (FileNotFoundException ex1) {
						}
					}
				}

				if (!success && !stdin && TMSS.DEFAULT_FILE_NAME.equals(s)) {
					try { // if no exception is thrown then the result is necessarily true
						success = (machine = new TMSS(TMSS.DEFAULT_FILE_NAME, true)) != null;
					} catch (FileNotFoundException ex) {
						try { // if no exception is thrown then the result is necessarily true
							success = (machine = new TMSS((TMSS.DEFAULT_FILE_NAME + ".txt"), true)) != null;
						} catch (FileNotFoundException ex1) {
						}
					}
				}
			}
		}
		machine = !success ? new TMSS() : machine;
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
							+ TMSS.DEFAULT_FILE_NAME + ".txt in the same directory.");
					System.out.println("Its previous contents were:\n" + s);
				} else {
					System.out.println("The description of the current machine was saved to " + TMSS.DEFAULT_FILE_NAME
							+ ".txt in the same directory.");
				}
			}
		}

		return machine;
	}

	public static TMSS main(TMSS m, String[] args) throws IllegalArgumentException {
		return TMSS.main(m, args, false);
	}

	public static TMSS main(TMSS m, boolean stdin) throws IllegalArgumentException {
		return TMSS.main(m, null, stdin);
	}

	public static TMSS main(String[] args, boolean stdin) throws IllegalArgumentException {
		return TMSS.main(null, args, stdin);
	}

	public static TMSS main(TMSS m) throws IllegalArgumentException {
		return TMSS.main(m, null, false);
	}

	// the version of main called by the Java compiler
	public static void main(String[] args) throws IllegalArgumentException {
		TMSS.main(null, args, false);
	}

	public static TMSS main(boolean stdin) throws IllegalArgumentException {
		return TMSS.main(null, null, stdin);
	}

	public static TMSS main() throws IllegalArgumentException {
		return TMSS.main(true);
	}

	public static TMSS main2(String fileName, boolean print, boolean save) throws IllegalArgumentException {
		String[] args = { fileName, Boolean.toString(print), save ? TMSS.SAVE : null };
		return TMSS.main(null, args);
	}

	public static TMSS main2(String fileName, boolean print) throws IllegalArgumentException {
		return TMSS.main2(fileName, print, false);
	}

	public static TMSS main2(String fileName) throws IllegalArgumentException {
		return TMSS.main2(fileName, false);
	}

	public static TMSS main3(String machineDescription, boolean print, boolean save) throws IllegalArgumentException {
		TMSS m = new TMSS(machineDescription);
		String[] args = { Boolean.toString(print), save ? TMSS.SAVE : null };
		return TMSS.main(m, args, true);
	}

	public static TMSS main3(String machineDescription, boolean print) throws IllegalArgumentException {
		return TMSS.main3(machineDescription, print, false);
	}

	public static TMSS main3(String machineDescription) throws IllegalArgumentException {
		return TMSS.main3(machineDescription, false);
	}
}
