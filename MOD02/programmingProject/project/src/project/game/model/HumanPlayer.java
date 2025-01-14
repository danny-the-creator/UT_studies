package project.game.model;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

/**
 * Represents a player of DotsAndBoxes game that implements the Player interface.
 * In this case, the player is a human, for this reason the most important method of this class
 * asks for input from the client.
 */
public class HumanPlayer extends AbstractPlayer {
    /**
     * Creates a new Player object.
     *
     * @param name   name of the player
     * @param colour the colour of the player
     */
    public HumanPlayer(String name, String colour) {
        super(name, colour);
    }

    /**
     * Ask player for the next move and send it to the server, where it is checked for being legal.
     *
     * @param game the current game
     * @return the player's choice
     */
    @Override
    public Move determineMove(Game game) {
        System.out.println("Enter your move: ");
        BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
        try {
            String input = in.readLine();
            if (game.isGameover()) {
                return null;
            }
            return new MoveDnB(this.getColour(), Integer.parseInt(input));
        } catch (IOException e) {
            throw new RuntimeException(e);
        } catch (NumberFormatException ignored) {
            return null;
        }
    }
}
