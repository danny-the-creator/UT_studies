package ss.project.game.model;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
/**
 * Represents a board for the DotAndBoxes game.
 */
public class BoardDnB {
    /**
     * Dimension of the board, i.e., if set to 5, the board has 5 rows, 5 columns and 60 lines (from 0 to 59).
     */
    public final int DIM = 2;
    private final String POINT = "*";

    /**
     * After constructor is called, here NumberBoard will be stored, which is going to show indexes of all lines.
     */
    public String EXAMPLE= null;
    /**
     * Represents all the lines of the chosen board.
     */
    public final List<String> LINES = new ArrayList<>();
    /**
     * Represents all the Boxes of the chosen board.
     */
    public final List<String> BOXES = new ArrayList<>();
    public final List<String> NUMBERS = new ArrayList<>();
    /**
     * Represents all the lines of the chosen board (ignoring the colour).
     */
    public List<String> EmptyLines= new ArrayList<>();    /**
     * Returns a String representation of this board (current situation).
     * @return the game situation as String
     */

    public String createBoard(){
        int num = 0;
        String board = POINT;
        for (int i=0 ; i<DIM; i++){

            for (int j=0; j<DIM; j++){
                board+=LINES.get(num)+POINT;
                num++;
            }
            board+="\n";
            for (int j=0; j<DIM; j++){
                board+=LINES.get(num)+BOXES.get(i*DIM+j);
                num++;
            }
            board+=LINES.get(num)+"\n"+POINT;
            num++;
        }
        for (int j=0; j<DIM; j++){
            board+=LINES.get(num)+POINT;
            num++;
        }
        return board;
    }
    /**
     * Returns a String representation of the board,but instead of lines it shows the indexes.
     * @return the board of numbers
     */
    public String createNumberBoard(){
        int num = 0;
        String board = POINT;
        for (int i=0 ; i<DIM; i++){

            for (int j=0; j<DIM; j++){
                board+=NUMBERS.get(num)+POINT;
                num++;
            }
            board+="\n";
            for (int j=0; j<DIM; j++){
                board+=NUMBERS.get(num)+ Components.EMPTY;
                num++;
            }
            board+=NUMBERS.get(num)+"\n"+POINT;
            num++;
        }
        for (int j=0; j<DIM; j++){
            board+=NUMBERS.get(num)+POINT;
            num++;
        }
        return board;
    }
    /**
     * Creates an empty board with the EXAMPLE.
     * Fills in all the lists.
     */
    public BoardDnB(){
        int num = 0;
        for (int i= 0; i<DIM;i++){      // this loop fills all the lists
            for (int j= 0;j<DIM;j++){
                BOXES.add(Components.EMPTY);
                LINES.add(Components.HORIZONTAL);
            }
            for (int j=0;j<DIM+1;j++){
                LINES.add(Components.VERTICAL);
            }
        }
        for (int j=0; j<DIM;j++){
            LINES.add(Components.HORIZONTAL);
        }

        for (int i=0; i<LINES.size();i++){      // this loop creates a list of indexes and insures they look good on the board
            if (LINES.get(i).equals(Components.HORIZONTAL)) {
                NUMBERS.add(String.format("%- 6d", i));
            }else {
                if (i<10){
                    NUMBERS.add(i+" ");
                } else {
                    NUMBERS.add(""+i);
                }
            }
        }
        EXAMPLE=createNumberBoard();
        EmptyLines = new ArrayList<>(LINES);
    }
    /**
     * Creates a deep copy of all lines and boxes.
     */
    public BoardDnB deepCopy(){
        BoardDnB board = new BoardDnB();
        for (int i=0; i< BOXES.size(); i++){
            board.BOXES.set(i, BOXES.get(i));
        }
        for (int i=0; i< LINES.size();i++)
            board.LINES.set(i, LINES.get(i));
        return board;
    }
    /**
     * Returns true if index is a valid index of a line on the board.
     * @return true if 0 <= index < 2*DIM*(DIM+1))
     */
    public boolean isField(int index){
        return (index >= 0 && index<2*DIM*(DIM+1));
    }
    /**
     * Returns the content of the line i.
     * @param i the number of the line
     * @return the colored line
     */
    public String getLine(int i){
        return LINES.get(i);
    }
    /**
     * Returns true if the field i is empty (the line is white).
     * @param i the index of the line.
     * @return true if the line is white
     */
    public boolean isEmptyField(int i) {
        return getLine(i).equals(Components.HORIZONTAL) || getLine(i).equals(Components.VERTICAL);
    }
    /**
     * Tests if the whole board is full.
     * @return true if all lines are colored
     */
    public boolean isFull() {
        for (int i=0; i<LINES.size();i++){
            if (isEmptyField(i)){
                return false;
            }
        }
        return true;
    }
    /**
     * Returns true if the game is over. The game is over when the whole board is full.
     * @return true if the game is over
     */
    public boolean gameOver() {
        return isFull();
    }

    /**
     * Returns which of the players has more boxes taken.
     * @return color of the winner
     */
    public String findWinner() {
        int bluePoints = 0;
        int redPoints = 0;
        for (String box: BOXES){
            // for each box the loop checks who has taken it and add a point to this player
            if (box.equals(Components.BLUE+ Components.TAKEN+ Components.RESET)){
                bluePoints++;
            } else if (box.equals(Components.RED+ Components.TAKEN+ Components.RESET)) {
                redPoints++;
            }
        }
        // returns the colour, which scored more points or Components.Reset if it is a draw
        if (bluePoints>redPoints){
            return Components.BLUE;
        } else if (redPoints>bluePoints){
            return Components.RED;
        } else { return Components.RESET;}

    }

    /**
     * Checks whether all sides of the square are colored.
     * Required for finishBox()
     * @param sides sides of a square
     * @return true if all sides of the square are colored.
     */
    private boolean checkSides(List<Integer> sides){
        for (int side : sides )
            if (!isField(side) || isEmptyField(side)){
                return false;
            }
        return true;
    }

    /**
     * Checks if the line with the index i finishes the box.
     * If so, the method paint the box, which was finished with the given colour.
     * @param i the index of the line
     * @param colour the colour, in which the taken box should be painted
     */
    public void finishBox (int i, String colour){
        List<Integer> sides;
        if (getLine(i).contains(Components.HORIZONTAL)){
            // Checks if the box below this line is finished.
            sides = new ArrayList<>(Arrays.asList(i+DIM, i+DIM+1, i+2*DIM+1));
            if (checkSides(sides)){
                // this formula computes which box was finished given the index of the top side
                BOXES.set((i/(2*DIM+1)*DIM + i%(2*DIM+1)), colour+ Components.TAKEN+ Components.RESET );
            }
            // Checks if the box above this line is finished.
            sides = new ArrayList<>(Arrays.asList(i-DIM, i-DIM-1, i-2*DIM-1));
            if (checkSides(sides)){
                // this formula computes which box was finished given the index of the bottom side
                BOXES.set((i/(2*DIM+1)*DIM + i%(2*DIM+1)-DIM),  colour+ Components.TAKEN+ Components.RESET );
            }
        } else if (getLine(i).contains(Components.VERTICAL)){
            // Checks if the box on the right side of this line is finished.
            sides = new ArrayList<>(Arrays.asList(i-DIM, i+1, i+DIM+1));
            if (getLine(i+1).contains(Components.VERTICAL) && getLine(i - DIM).contains(
                    Components.HORIZONTAL) && checkSides(sides)) { // first two conditions are made
                // for the edgeCase, i.e., if the box on the right side of this line doesn't exist
                // this formula computes which box was finished given the index of the left side
                BOXES.set(((i-DIM)/(2*DIM+1)*DIM + (i-DIM)%(2*DIM+1)),  colour+ Components.TAKEN+ Components.RESET);
            }
            // Checks if the box on the left side of this line is finished.
            sides = new ArrayList<>(Arrays.asList(i-DIM-1, i-1, i+DIM));
            if (getLine(i - 1).contains(Components.VERTICAL) && getLine(i - DIM-1).contains(
                    Components.HORIZONTAL) && checkSides(sides)) {// first two conditions are made
                // for the edgeCase, i.e., if the box on the left side of this line doesn't exist
                // this formula computes which box was finished given the index of the right side
                BOXES.set(((i-DIM-1)/(2*DIM+1)*DIM + (i-DIM-1)%(2*DIM+1)),  colour+ Components.TAKEN+ Components.RESET);
            }
        }
    }

    /**
     * Empties all lines and all boxes of this board (i.e., let them refer to the white colour).
     */
    public void reset(){
        for (int i=0; i< BOXES.size(); i++){
            BOXES.set(i, Components.EMPTY);
        }
        for (int i=0; i< LINES.size();i++)
            LINES.set(i, EmptyLines.get(i));
    }
    /**
     * Paints the content of LINES i to the chosen colour.
     * Moreover,it checks if the given line finished the box.
     * @param i the index of the line
     * @param colour the colour, in which this line should be painted
     * @return true if the box was finished (i.e., if the list of boxes has changed)
     */
    public boolean setField(int i, String colour){
        List<String> oldBoxes = new ArrayList<>(BOXES);     // makes a copy of the Boxes
        LINES.set(i,colour+EmptyLines.get(i)+ Components.RESET);
        finishBox(i, colour);
        return oldBoxes.equals(BOXES);      // compares BOXES with the copy, which was made earlier
    }
}