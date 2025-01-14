package project.test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import project.game.model.*;

import static org.junit.jupiter.api.Assertions.*;
/**
 * The GameDnBTest class is a JUnit test class for the GameDnB class.
 * It contains various tests to ensure the correct functionality of the GameDnB class methods.
 */
public class GameDnBTest {
    private GameDnB game;
    /**
     * Sets up the initial conditions for each test case, including creating an instance of the
     * GameDnB class and initializing player objects and the current player.
     */
    @BeforeEach
    public void setUp(){
        game = new GameDnB();
        game.player1 = new HumanPlayer("biba", Components.BLUE);
        game.player2 = new HumanPlayer("boba", Components.RED);
        game.current = game.player1;
    }
    /**
     * Test case to check the validity of a move in the game.
     * It verifies if a move is considered valid or invalid based on DotsAndBoxes rules
     * and on the game state.
     */
    @Test
    public void testIsValidMove(){
        assertTrue(game.isValidMove(new MoveDnB(Components.RED, 0)));
        assertTrue(game.isValidMove(new MoveDnB(Components.BLUE, 0)));
        assertFalse(game.isValidMove(new MoveDnB(Components.RED, -1)));
        assertTrue(game.isValidMove(new MoveDnB(Components.RED, 2* game.getBoard().DIM*(game.getBoard().DIM+1)-1)));// the last line of the board
        assertFalse(game.isValidMove(new MoveDnB(Components.RED, 2* game.getBoard().DIM*(game.getBoard().DIM+1))));// the last line of the board +1
        assertTrue(game.isValidMove(new MoveDnB(Components.RED, 3)));
        game.doMove(new MoveDnB(Components.BLUE, 3));
        // ensures we cannot colour the line, which is already colored
        assertFalse(game.isValidMove(new MoveDnB(Components.RED, 3)));
    }
    /**
     * Test case to retrieve a list of ValidMoves in the current game state.
     * It ensures that the list only contains valid move locations and is appropriately
     * update after moves are made.
     */
    @Test
    public void testGetValidMoves(){
        List<? extends Move> validMoves = game.getValidMoves();     // a copy of the ValidMoves
        // ensures that all move on the board are valid, since no lines are colored
        assertEquals(2* game.getBoard().DIM*(game.getBoard().DIM+1), validMoves.size());
        for (Move move: validMoves){
            //shows that validMoves doesn't contain invalid moves
            assertNotEquals(-1,move.getLocation());
            assertNotEquals(2* game.getBoard().DIM*(game.getBoard().DIM+1), move.getLocation());
        }
        game.doMove(new MoveDnB(game.getTurn().getColour(), 0));
        game.doMove(new MoveDnB(game.getTurn().getColour(), 2*game.getBoard().DIM*(game.getBoard().DIM+1)-1));
        assertEquals(validMoves.size()-2, game.getValidMoves().size());
        for (Move move: game.getValidMoves()){
            //shows that validMoves doesn't contain moves, that were already played
            assertNotEquals(0, move.getLocation());
            assertNotEquals(2*game.getBoard().DIM*(game.getBoard().DIM+1)-1, move.getLocation());
        }
    }
    /**
     * Test case to determine the winner of the game.
     * It checks if the correct winner is identified based on the moves made on the board.
     */
    @Test
    public void testWinner(){
        // color all sides of the first BOX
        game.doMove(new MoveDnB(game.getTurn().getColour(),0));
        game.doMove(new MoveDnB(game.getTurn().getColour(), game.getBoard().DIM));
        game.doMove(new MoveDnB(game.getTurn().getColour(), game.getBoard().DIM+1));
        game.doMove(new MoveDnB(Components.BLUE,2* game.getBoard().DIM+1));
        // ensures that the winner is the one, who coloured the last side of the box
        assertNotEquals(Components.RED, game.getWinner().getColour());
        assertEquals(Components.BLUE, game.getWinner().getColour());
        game.getBoard().reset();
        // shows that after reset no one is winner
        assertNull(game.getWinner());
    }

    /**
     * Test case to check if the game is over.
     * It verifies whether the whole board is covered or not
     */
    @Test
    public void testGameOver(){
        for (int i = 0; i<2* game.getBoard().DIM*(game.getBoard().DIM+1); i++ ){
            assertFalse(game.isGameover());
            game.doMove(new MoveDnB(game.getTurn().getColour(), i));
        }
        assertTrue(game.isGameover());


    }
    /**
     * Test case to create a deep copy of the game and validate its independence.
     * It checks if modifying the deep copy does not affect the original game state.
     */
    @Test
    public void testDeepCopy(){
        Game newgame = game.deepCopy();
        // ensures that deepCopy of the board works
        assertNotEquals(game.getBoard(), newgame.getBoard());
        assertEquals(game.getBoard().LINES, newgame.getBoard().LINES);// all lines are equal
        assertEquals(game.getBoard().BOXES, newgame.getBoard().BOXES);// all boxes are equal
        assertEquals(game.getTurn(), newgame.getTurn());//current players are equal
        game.doMove(new MoveDnB(game.getTurn().getColour(), 0));
        assertNotEquals(game.getBoard(), newgame.getBoard());
        assertNotEquals(game.getBoard().LINES, newgame.getBoard().LINES);
        assertNotEquals(game.getTurn(), newgame.getTurn());
        newgame.doMove(new MoveDnB(game.getTurn().getColour(), game.getBoard().DIM));
        assertNotEquals(game.getBoard(), newgame.getBoard());
        assertNotEquals(game.getBoard().LINES, newgame.getBoard().LINES);
        assertEquals(game.getTurn(), newgame.getTurn());


    }
    /**
     * Test case to retrieve the current turn in the game.
     * It checks if the correct player is identified as the current one.
     */
    @Test
    public void testGetTurn(){
        assertEquals(game.getTurn(), game.player1); // ensures the player1 starts first
        game.doMove(new MoveDnB(game.getTurn().getColour(), 0));
        // ensures that players take turns based on DotsAndBoxes rules
        assertEquals(game.getTurn(), game.player2);
        game.doMove(new MoveDnB(game.getTurn().getColour(), game.getBoard().DIM));
        assertNotEquals(game.getTurn(), game.player2);
        game.doMove(new MoveDnB(game.getTurn().getColour(), game.getBoard().DIM+1));
        assertEquals(game.getTurn(), game.player2);
        game.doMove(new MoveDnB(game.getTurn().getColour(), 2* game.getBoard().DIM+1));
        // ensures that after finishing the box, the player continues his turn
        assertEquals(game.getTurn(), game.player2);
    }

    /**
     * Test case to check if a move input string is parsed correctly.
     * Moreover, it checks if the correct exception is called if the input is wrong
     */
    @Test
    public void testCheckMove() throws NotValidMove {
        assertEquals(0,game.checkMove("0").getLocation());
        assertEquals(game.getBoard().DIM, game.checkMove(""+game.getBoard().DIM).getLocation());
        // ensures that if move is invalid then an exception is thrown
        assertThrows(NotValidMove.class, () -> game.checkMove("-1"));
        assertThrows(NotValidMove.class, () -> game.checkMove(""+(2*game.getBoard().DIM)*(game.getBoard().DIM+1)));
        assertThrows(NumberFormatException.class, () -> game.checkMove("Hello World!"));
    }
    /**
     * Test case to simulate and validate a game with a smaller board size (DIM=2).
     * It checks various game aspects, such as moves, turns, winners, and game over conditions.
     */
    @Test
    public void testPlayGameDIM2(){
        // to run this test a variable "DIM" in BoardDnB should be set to 2
        List<String> oldLines = new ArrayList<>(game.getBoard().LINES);
        // checks if toString function works
        assertTrue(game.toString().contains(game.getTurn().getName()));
        assertEquals(oldLines, game.getBoard().LINES);
        assertEquals(game.getTurn(), game.player1);
        assertNull(game.getWinner());
        assertFalse(game.isGameover());
        // Move #1
        game.doMove(new MoveDnB(game.getTurn().getColour(), 0));
        // ensures that Move "0" is now invalid
        assertFalse(game.isValidMove(new MoveDnB(game.getTurn().getColour(), 0)));
        // ensures that players take turns according to the rules
        assertEquals(game.getTurn(), game.player2);
        // Move #2
        game.doMove(new MoveDnB(game.getTurn().getColour(), 3));
        assertNotEquals(game.getTurn(), game.player2);
        // Move #3
        game.doMove(new MoveDnB(game.getTurn().getColour(), 5));
        assertEquals(game.getTurn(), game.player2);
        // Move #4
        game.doMove(new MoveDnB(game.getTurn().getColour(), 2));
        // ensures that one of the boxes is taken by the player2
        assertEquals(game.getTurn(), game.player2);
        assertEquals(game.getWinner(), game.player2);
        assertTrue(game.isValidMove(new MoveDnB(game.getTurn().getColour(), 7)));
        // Move #5
        game.doMove(new MoveDnB(game.getTurn().getColour(), 7));
        assertEquals(game.getTurn(), game.player1);
        // Move #6
        game.doMove(new MoveDnB(game.getTurn().getColour(), 4));
        assertNotEquals(game.getTurn(), game.player1);
        // Move #7
        game.doMove(new MoveDnB(game.getTurn().getColour(), 6));
        assertEquals(game.getTurn(), game.player1);
        // Move #8
        game.doMove(new MoveDnB(game.getTurn().getColour(), 1));
        //ensures that player1 has taken the box
        assertEquals(game.getTurn(), game.player1);
        // Move #9
        game.doMove(new MoveDnB(game.getTurn().getColour(), 10));
        assertEquals(game.getTurn(), game.player2);
        assertNull(game.getWinner());
        // Move #10
        game.doMove(new MoveDnB(game.getTurn().getColour(), 8));
        // ensures that player2 has taken the second box
        assertEquals(game.getTurn(), game.player2);
        assertNotEquals(game.getTurn(), game.player1);
        assertEquals(game.getWinner(), game.player2);
        // Move #11
        game.doMove(new MoveDnB(game.getTurn().getColour(), 9));
        assertEquals(game.getTurn(), game.player1);
        // shows that game is still not over
        assertFalse(game.isGameover());
        // Move #12
        game.doMove(new MoveDnB(game.getTurn().getColour(), 11));
        // ensures that the game has ended with the draw
        assertNull(game.getWinner());
        // ensures that there are no valid moves left
        assertTrue(game.getValidMoves().isEmpty());
        // ensures that game is over
        assertTrue(game.isGameover());
        assertNotEquals(game.getWinner(), game.player2);
        assertNotEquals(game.getWinner(), game.player1);
        //ensures that the lines have changed,but after the reset they return to their initial state
        assertNotEquals(oldLines, game.getBoard().LINES);
        game.getBoard().reset();
        assertEquals(oldLines, game.getBoard().LINES);
    }
}
