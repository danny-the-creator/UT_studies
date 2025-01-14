package ss.project.game.ai;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import ss.project.game.model.BoardDnB;
import ss.project.game.model.Game;
import ss.project.game.model.Move;
/**
 * The smartest strategy with the hard difficulty.
 * It chooses a random move from all ValidMoves, which don't let the opponent score a point,
 * unless there are no choice , however if it can finish the box this turn,
 * the strategy will return this move
 */
public class StrategyLvlHard implements Strategy{
    /**
     * Returns the difficulty.
     * Shows how easy this strategy is.
     * @return the difficulty of the Strategy.
     */
    @Override
    public String getDifficulty() {
        return "Hard";
    }
    /**
     * If a player can finish a box on this turn, then this move will be returned,
     * otherwise it will choose any move, which don't allow opponent to score a point, if there are
     * no such moves left, it will proceed as StrategyLvlEasy.
     * @param game current state of the game
     * @return the best move based on the strategy
     */
    @Override
    public Move determineMove(Game game) {
        if (game.isGameover()){// Since the game is played on the server, the program can try
            // to determine the move, when the game is over. It results into an error,
            // so we deal with that here
            return null;
        }
        Random random = new Random();
        List<Move> allowedMoves = new ArrayList<>();
        Move scoreMove = findScoreMove(game);
        if (scoreMove!=null){
            return scoreMove;
        }
        for (Move move: game.getValidMoves()){
            Game gameCopy = game.deepCopy();
            gameCopy.doMove(move);
            if (findScoreMove(gameCopy)==null){
                allowedMoves.add(move);
            }
        }
        if (allowedMoves.isEmpty()){
            return game.getValidMoves().get(random.nextInt(game.getValidMoves().size()));
        }
        return allowedMoves.get(random.nextInt(allowedMoves.size()));
    }
    /**
     * Returns a move, which finishes one or several boxes.
     * @param game the current game
     * @return the move, which will give you a point
     */
    private Move findScoreMove(Game game){
        for (Move m: game.getValidMoves()){
            BoardDnB boardCopy = game.getBoard().deepCopy();
            if (!boardCopy.setField(m.getLocation(),m.getColour())){
                return m;
            }
        }
        return null;
    }
}
