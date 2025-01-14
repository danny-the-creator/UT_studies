package ss.tictactoe.ai;

import ss.tictactoe.ai.Strategy;
import ss.tictactoe.model.Game;
import ss.tictactoe.model.Move;

public class NaiveStrategy implements Strategy {
    @Override
    public String getName() {
        return "Naive";
    }

    @Override
    public Move determineMove(Game game) {
        return game.getValidMoves().get(( int)(Math.random() * game.getValidMoves().size()));
    }
}
