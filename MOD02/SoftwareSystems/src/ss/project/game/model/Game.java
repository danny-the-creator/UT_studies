package ss.project.game.model;

import java.util.List;
import ss.project.game.model.BoardDnB;
import ss.project.game.model.Move;
import ss.project.game.model.Player;

/**
 * A simple turn-based game.
 */
public interface Game {
    //@ instance invariant !isGameover() ==> getValidMoves().size() > 0;
    //@ instance invariant !isGameover() ==> getTurn() != null;

    /**
     * Check if the game is over, i.e., no more moves are available.
     * @return whether the game is over
     */
    //@ pure;
    boolean isGameover();

    /**
     * Query whose turn it is.
     * @return the player whose turn it is
     */
    //@ pure;
    Player getTurn();

    /**
     * Get the winner of the game. If the game is a draw, then this method returns null.
     * @return the winner, or null if no player is the winner
     */
    //@ pure;
    Player getWinner();

    /**
     * Return all moves that are valid in the current state of the game.
     * @return the list of currently valid moves
     */
    //@ ensures (\forall Move m; \result.contains(m); isValidMove(m));
    //@ pure;
    List<? extends Move> getValidMoves();

    /**
     * Check if a move is a valid move.
     * @param move the move to check
     * @return true if the move is a valid move
     */
    //@ ensures \result <==> (\exists Move m; getValidMoves().contains(m); m.equals(move));
    //@ pure;
    boolean isValidMove(Move move);

    /**
     * Perform the move, assuming it is a valid move.
     * Changes the players turn if no boxes are painted.
     * @param move the move to play
     */
    //@ requires isValidMove(move);
    void doMove(Move move);

    /**
     * Creates a deepCopy of the board with all moves, which were played.
     * @return board deepCopy of the current board
     */
    BoardDnB getBoard();

    /**
     * Creates a deepCopy of the game, including board with all played moves, a copy of both players
     * and the copy of the current player.
     * @return game deepCopy of the current game
     */
    Game deepCopy();

    /**
     * Check ig the given index is valid for the game. If so, then returns the move.
     * If move is not valid then throws an Exception.
     * @param index String representation of the index on the board, which should be colored;
     * @return the move with the given location and colour of the current player
     * @throws NotValidMove if the move is illegal
     * @throws NumberFormatException if the given index is a number
     */

    Move checkMove(String index) throws NotValidMove, NumberFormatException;
}
