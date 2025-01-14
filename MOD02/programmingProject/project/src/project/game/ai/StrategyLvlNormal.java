package project.game.ai;

import java.util.Random;
import project.game.model.BoardDnB;
import project.game.model.Game;
import project.game.model.Move;

/**
 * The strategy with the normal difficulty.
 * It chooses a random move from all ValidMoves, however if it can finish the box, it will do it
 */
public class StrategyLvlNormal implements Strategy {
    /**
     * Returns the difficulty.
     * Shows how easy this strategy is.
     *
     * @return the difficulty of the Strategy.
     */
    @Override
    public String getDifficulty() {
        return "Normal";
    }

    /**
     * If a player can finish a box on this turn, then this move will be returned,
     * otherwise it will proceed as StrategyLvlEasy.
     *
     * @param game current state of the game
     * @return the best move based on the strategy
     */
    @Override
    public Move determineMove(Game game) {
        if (game.isGameover()) {      // Since the game is played on the server, the program can try
            // to determine the move, when the game is over. It results into an error,
            // so we deal with that here
            return null;
        }
        Random random = new Random();
        Move scoreMove = findScoreMove(game);
        if (scoreMove != null) {
            return scoreMove;
        }

        return game.getValidMoves().get(random.nextInt(game.getValidMoves().size()));

    }

    /**
     * Returns a move, which finishes one or several boxes.
     *
     * @param game the current game
     * @return the move, which will give you a point
     */
    private Move findScoreMove(Game game) {
        for (Move m : game.getValidMoves()) {
            BoardDnB boardCopy = game.getBoard().deepCopy();
            if (!boardCopy.setField(m.getLocation(), m.getColour())) {
                return m;
            }
        }
        return null;
    }
}
