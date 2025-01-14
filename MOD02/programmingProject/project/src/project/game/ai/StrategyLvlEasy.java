package project.game.ai;

import java.util.Random;
import project.game.model.Game;
import project.game.model.Move;

/**
 * The simplest strategy with the lowest difficulty.
 * It chooses a random move from all ValidMoves
 */
public class StrategyLvlEasy implements Strategy {
    /**
     * Returns the difficulty.
     * Shows how easy this strategy is.
     *
     * @return the difficulty of the Strategy.
     */
    @Override
    public String getDifficulty() {
        return "Easy";
    }

    /**
     * Returns a random move from all ValidMoves.
     *
     * @param game current state of the game
     * @return the best move based on the strategy
     */
    @Override
    public Move determineMove(Game game) {
        if (game.isGameover()) {// Since the game is played on the server, the program can try
            // to determine the move, when the game is over. It results into an error,
            // so we deal with that here
            return null;
        }
        Random random = new Random();
        return game.getValidMoves().get(random.nextInt(game.getValidMoves().size()));
    }
}
