package ss.tictactoe.ai;

import ss.tictactoe.model.AbstractPlayer;
import ss.tictactoe.model.Game;
import ss.tictactoe.model.Mark;
import ss.tictactoe.model.Move;

public class ComputerPlayer extends AbstractPlayer {
    Strategy strategy;
    /**
     * Creates a new Player object.
     *
     * @param strategy
     * @param mark
     */
    public ComputerPlayer(Mark mark, Strategy strategy) {
        super(strategy.getName()+"-"+mark.toString(), mark);
        this.strategy = strategy;
    }
    @Override
    public Move determineMove(Game game) {
        return strategy.determineMove(game);
    }

    public Strategy getStrategy() {
        return strategy;
    }

    public void setStrategy(Strategy strategy) {
        this.strategy = strategy;
    }
}
