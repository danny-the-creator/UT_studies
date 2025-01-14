package project.game.ai;

import java.util.concurrent.TimeUnit;
import project.game.model.AbstractPlayer;
import project.game.model.Game;
import project.game.model.Move;


/**
 * Represents a player of DotsAndBoxes game that implements the Player interface.
 * In this case, the player is an AI with different difficulties. To be able to play on a server
 * with this AI, a delay before determining each move is created.
 */
public class ComputerPlayer extends AbstractPlayer {
    Strategy strategy;

    /**
     * Creates a new Player object. Name represents the level of the AI.
     * It is shown only for the player, who is using this AI
     *
     * @param strategy the strategy the AI will use
     * @param colour   the colour the AI will use
     */
    public ComputerPlayer(String colour, Strategy strategy) {
        super("AI-" + strategy.getDifficulty(), colour);
        this.strategy = strategy;
    }

    /**
     * Waits for server to response after that determines the next move based
     * on the strategy (difficulty level) the AI is using.
     *
     * @param game the current game
     * @return the move the AI wants to play
     */
    @Override
    public Move determineMove(Game game) {
        // a delay so that we could get response from the server before determining the next move
        try {
            TimeUnit.MILLISECONDS.sleep(250);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
        return strategy.determineMove(game);
    }

    /**
     * Returns the strategy of the AI. (for future improvements)
     *
     * @return the strategy of the AI
     */
    public Strategy getStrategy() {
        return strategy;
    }

    /**
     * Sets the strategy of the AI. (for future improvements)
     *
     * @param strategy the strategy the AI will use
     */
    public void setStrategy(Strategy strategy) {
        this.strategy = strategy;
    }
}
