package project.game.ai;


import project.game.model.Game;
import project.game.model.Move;

/**
 * A strategy for turn-based game.
 */
public interface Strategy {
    /**
     * returns the difficulty of the AI player.
     * @return String name
     */
    //@pure;
    String getDifficulty();

    /**
     * determines the next move based on the strategy.
     * @param game current state of the game
     * @return move next move that needs to be played based on the strategy
     */
    //@requires game!= null;
    //@ensures game.isValidMove(\result);
    Move determineMove(Game game);
}
