package ss.tictactoe.ai;

import java.util.ArrayList;
import java.util.List;
import ss.tictactoe.model.*;

public class SmartStrategy implements  Strategy {
    private List<Move> allowedMoves = new ArrayList<>(List.of());

    @Override
    public String getName() {
        return "Smart";
    }

    @Override
    public Move determineMove(Game game) {
        allowedMoves = new ArrayList<>(List.of());
        Move winMove = findWinningMove(game);
        if (winMove != null) {
            return winMove;
        }
        for (Move i : game.getValidMoves()) {
            Game gameCopy = game.deepCopy();
            gameCopy.doMove(i);
            if (findWinningMove(gameCopy) == null){
                allowedMoves.add(i);
            }
        }
        if (allowedMoves.isEmpty()) {
            return game.getValidMoves().get((int) (Math.random() * game.getValidMoves().size()));
        }
        return allowedMoves.get((int) (Math.random() * allowedMoves.size()));
    }
    private Move findWinningMove(Game game) {
        for (Move i : game.getValidMoves()) {
            Board boardCopy = game.getBoard().deepCopy();
            boardCopy.setField(i.getLocation(), i.getMark());
            if (boardCopy.isWinner(i.getMark())) {
                return i;
            }
        }
        return null;
    }
}