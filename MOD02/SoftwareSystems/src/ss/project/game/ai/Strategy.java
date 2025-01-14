package ss.project.game.ai;


import ss.project.game.model.Game;
import ss.project.game.model.Move;

/**
 * A strategy for turn-based game.
 */
public interface Strategy {
    /**
     * returns the difficulty of the ai player.
     * @return String name
     */
    //@pure;
    public String getDifficulty();

    /**
     * determines the next move based on the strategy.
     * @param game current state of the game
     * @return move next move that needs to be played based on the strategy
     */
    //@requires game!= null;
    //@ensures game.isValidMove(\result);
    public Move determineMove(Game game);
}
