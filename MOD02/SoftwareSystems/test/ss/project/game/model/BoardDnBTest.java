package ss.project.game.model;

import java.util.ArrayList;
import java.util.List;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import ss.project.server.Protocol;
import ss.tictactoe.model.Board;
import ss.tictactoe.model.Mark;

import static org.junit.jupiter.api.Assertions.*;
import static org.junit.jupiter.api.Assertions.assertEquals;
/**
 * The BoardDnBTest class is a JUnit test class for the BoardDnB class.
 * It contains various tests to ensure the correct functionality of the BoardDnB class methods.
 */
public class BoardDnBTest {
    private BoardDnB board;

    @BeforeEach
    public void setUp() {
        board = new BoardDnB();
    }
    /**
     * Test case to verify if a field index is within the valid range.
     * It checks both lower and upper bounds of the field index.
     */
    @Test
    public void testIsFieldIndex() {
        assertFalse(board.isField(-1));
        assertTrue(board.isField(0));
        assertTrue(board.isField(2*board.DIM * (board.DIM + 1)-1)); // the last line
        assertFalse(board.isField(2*board.DIM * (board.DIM + 1)));// the last line +1
    }

    /**
     * Test case to set and get values at specific field indices.
     * It verifies the correct setting and retrieval of values at specified indices.
     */
    @Test
    public void testSetAndGetFieldIndex() {
        board.setField(0, Components.RED);
        assertEquals(Components.RED+Components.HORIZONTAL+Components.RESET, board.getLine(0));
        assertEquals(Components.VERTICAL, board.getLine(board.DIM));
    }
    /**
     * Test case to reset the board to its initial state and verify the reset.
     * It ensures that the board is reset to its original configuration.
     */
    @Test
    public void testReset() {
        assertTrue(board.createBoard().contains(Components.HORIZONTAL));
        board.setField(0, Components.BLUE);
        board.setField(board.DIM, Components.RED);
        board.setField(2*board.DIM*(board.DIM+1)-1, Components.RED);
        board.reset();
        assertEquals(Components.HORIZONTAL, board.getLine(0));
        assertEquals(Components.VERTICAL, board.getLine(Board.DIM));
        assertEquals(Components.HORIZONTAL, board.getLine(2*board.DIM*(board.DIM+1)-1));
    }
    /**
     * Test case to create a deep copy of the board and validate its independence.
     * It checks if modifying the deep copy does not affect the original board.
     */
    @Test
    public void testDeepCopy() {
        board.setField(0, Components.BLUE);
        board.setField(Board.DIM * Board.DIM - 1,Components.RED);
        BoardDnB deepCopyBoard = board.deepCopy();

        // First test if all the fields are the same
        for (int i = 0; i < Board.DIM * Board.DIM; i++) {
            assertEquals(board.getLine(i), deepCopyBoard.getLine(i));
        }

        // Check if a field in the deepcopied board the original remains the same
        deepCopyBoard.setField(0, Components.RED);
        // "Components.BLUE+Components.HORIZONTAL+Components.RESET" is a string, which represents the colored line
        assertEquals(Components.BLUE+Components.HORIZONTAL+Components.RESET, board.getLine(0));
        assertEquals(Components.RED+Components.HORIZONTAL+Components.RESET, deepCopyBoard.getLine(0));
    }
    /**
     * Test case to check if a field index is empty.
     * It verifies the correct identification of empty and non-empty fields.
     */
    @Test
    public void testIsEmptyFieldIndex() {
        board.setField(0, Components.BLUE);
        assertFalse(board.isEmptyField(0));
        assertTrue(board.isEmptyField(1));
    }
    /**
     * Test case to check if the board is full.
     * It ensures the correct detection of a fully filled board.
     */

    @Test
    public void testIsFull() {
        for (int i = 0; i < 2*board.DIM * (board.DIM+1) - 1; i++) {
            // we colour all the lines, except one
            board.setField(i, Components.BLUE);
        }
        assertFalse(board.isFull());
        // here we colour the final line
        board.setField(2*board.DIM * (board.DIM+1) - 1,Components.RED);
        assertTrue(board.isFull());
    }
    /**
     * Test case to check if the game is over.
     * It verifies whether the game over condition is correctly determined.
     */
    @Test
    public void testGameOver(){
        for (int i = 0; i < 2*board.DIM * (board.DIM+1) - 1; i++) {
            // we colour all the lines, except one
            board.setField(i, Components.BLUE);
        }
        assertFalse(board.gameOver());
        board.setField(2*board.DIM * (board.DIM+1) - 1, Components.RED);
        // here we colour the final line
        assertTrue(board.gameOver());
    }
    /**
     * Test case to validate the finishing of a box on the board.
     * It checks if finishing a box updates the BOXES list accordingly.
     */
    @Test
    void testFinishBOx(){
        assertFalse(board.BOXES.contains(Components.TAKEN)); // ensures no boxes are taken
        assertTrue(board.BOXES.contains(Components.EMPTY));
        List<String> oldBoxes = new ArrayList<>(board.BOXES); // makes a copy of the boxes
        // here we colour all the lines of the first square and check that after 3 lines
        // BOXES haven't changed, but after the last side was coloured the boxes were changed
        // and now this box is taken by RED player
        board.setField(0, Components.RED);
        assertEquals(oldBoxes, board.BOXES);
        board.setField(board.DIM, Components.RED);
        assertEquals(oldBoxes, board.BOXES);
        board.setField(board.DIM+1, Components.RED);
        assertEquals(oldBoxes, board.BOXES);
        board.setField(2* board.DIM+1, Components.RED);
        assertNotEquals(oldBoxes, board.BOXES);
        assertTrue(board.BOXES.contains(Components.RED+Components.TAKEN+Components.RESET));
    }
    /**
     * Test case to determine the winner on the board.
     * It checks if the correct winner is identified based on the board state.
     */
    @Test
    public void testGetWinner() {
        // ensures that on the start no one is winner
        assertEquals(board.findWinner(), Components.RESET);
        // here we set all sides of the first box, so the BLUE player takes this box
        board.setField(0, Components.BLUE);
        board.setField(board.DIM, Components.BLUE);
        board.setField(board.DIM+1, Components.BLUE);
        board.setField(2* board.DIM+1, Components.BLUE);
        // ensures the BLUE player is a winner for now
        assertEquals(board.findWinner(), Components.BLUE);

    }

}
