package project.game.model;

import java.util.ArrayList;
import java.util.List;

/**
 * The GameDnB class represents a game of DotsAndBoxes that implements the Game interface.
 * It includes functionality for managing players, the game board,
 * turns, moves, and checking for the game's end.
 */
public class GameDnB implements Game {
    BoardDnB board = new BoardDnB();
    /**
     * Player representing the BLUE color.
     */
    public Player player1;
    /**
     * Player representing the RED color.
     */
    public Player player2;
    /**
     * Player whose turn it is.
     */
    public Player current;

    /**
     * Checks if the game is over.
     *
     * @return true if the game is over, false otherwise.
     */
    @Override
    public boolean isGameover() {
        return board.gameOver();
    }

    /**
     * Gets the player whose turn it is.
     *
     * @return The current player.
     */
    @Override
    public Player getTurn() {
        return current;
    }

    /**
     * Gets the winner of the game.
     *
     * @return The winning player or null if that is a draw.
     */
    @Override
    public Player getWinner() {
        String winner = board.findWinner();
        if (winner.equals(Components.BLUE)) {
            return player1;
        } else if (winner.equals(Components.RED)) {
            return player2;
        }
        return null;
    }

    /**
     * Gets a list of valid moves for the current turn.
     *
     * @return List of valid moves.
     */
    @Override
    public List<? extends Move> getValidMoves() {
        List<Move> validMoves = new ArrayList<>();
        Move move;
        for (String x : board.NUMBERS) {
            x = x.replace(" ", "");
            move = new MoveDnB(current.getColour(), Integer.parseInt(x));
            if (isValidMove(move)) {
                validMoves.add(move);
            }
        }
        return validMoves;
    }

    /**
     * Checks if a given move is valid.
     *
     * @param move The move to be validated.
     * @return true if the move is valid, false otherwise.
     */
    @Override
    public boolean isValidMove(Move move) {
        return board.isField(move.getLocation()) && board.isEmptyField(move.getLocation());
    }

    /**
     * Performs the specified move on the board.
     * Changes current player if no boxes were painted during this turn.
     *
     * @param move The move to be executed.
     */
    @Override
    public void doMove(Move move) {
        if (board.setField(move.getLocation(), move.getColour())) {
            // paints the chose line and checks if no boxes were painted
            if (getTurn() == player1) {
                current = player2;
            } else {
                current = player1;
            }
        }
    }

    /**
     * Gets the DnB board of the current game.
     *
     * @return The DnB board.
     */
    @Override
    public BoardDnB getBoard() {
        return this.board;
    }

    /**
     * Returns a string representation of the current game state.
     *
     * @return A string containing the board and information about the current turn.
     */
    @Override
    public String toString() {
        return board.EXAMPLE + "\n\n" + board.createBoard() + "\n" + "Current Player: " +
                current.getColour() + current.getName() + Components.RESET;
    }

    /**
     * Creates a deep copy of the current game.
     *
     * @return A new instance of GameDnB with the same state as the current game.
     */
    @Override
    public Game deepCopy() {
        GameDnB newGame = new GameDnB();
        newGame.board = getBoard().deepCopy();
        newGame.player1 = this.player1;
        newGame.player2 = this.player2;
        newGame.current = this.current;
        return newGame;
    }

    /**
     * Check ig the given index is valid for the game. If so, then returns the move.
     * If move is not valid then throws an Exception.
     *
     * @param index String representation of the index on the board, which should be colored;
     * @return the move with the given location and colour of the current player
     * @throws NotValidMove          if the move is illegal
     * @throws NumberFormatException if the given index is a number
     */
    @Override
    public Move checkMove(String index) throws NotValidMove, NumberFormatException {
        Move move = new MoveDnB(this.getTurn().getColour(), Integer.parseInt(index));
        if (!isValidMove(move)) {       // if the Move is illegal, then throws NotValidMove
            throw new NotValidMove();
        }
        return move;
    }
}