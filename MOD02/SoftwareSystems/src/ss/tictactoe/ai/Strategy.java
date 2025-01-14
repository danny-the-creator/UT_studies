package ss.tictactoe.ai;

import ss.tictactoe.model.Game;
import ss.tictactoe.model.Move;

public interface Strategy {
    /**
     * returns name of the strategy;
     * @return String name
     */
    //@pure;
    public String getName();

    /**
     * determines the next move based on the strategy
     * @param game current state of the game
     * @return move next move that needs to be played based on the strategy
     */
    //@requires game!= null;
    //@ensures game.isValidMove(\result);
    public Move determineMove(Game game);
}
