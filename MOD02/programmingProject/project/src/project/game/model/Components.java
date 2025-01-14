package project.game.model;

/**
 * Represents a combination of all possible values of the board in the DotsAndBoxes game, including
 * colors (3 possible values): Components.RED, Components.BLUE, Components.RESET;
 * lines (2 possible values): Components.HORIZONTAL, Components.VERTICAL;
 * boxes (2 possible values): Components.TAKEN, Components.EMPTY;
 */
public class Components {
    //Colors the next string in Red if is added before.
    public static final String RED = "\u001B[31m";
    //Colors the next string in Blue if is added before.
    public static final String BLUE = "\u001B[36m";
    //Reset the colour of the string back to White.
    public static final String RESET = "\u001B[0m";
    public static final String HORIZONTAL = "-----";
    public static final String VERTICAL = "|";
    public static final String TAKEN = " XXX ";

    public static final String EMPTY = "     ";

}