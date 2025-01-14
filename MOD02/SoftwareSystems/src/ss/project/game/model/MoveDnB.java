package ss.project.game.model;
/**
 * A move in a DotAndBoxes game.
 */
public class MoveDnB implements Move {
    String colour;
    int location;

    /**
     * Constructs an object, called MoveDnB, and sets the colour and the location of the move.
     * @param colour colour of the move
     * @param location location of the move
     */
    public MoveDnB(String colour, int location){
        this.colour=colour;
        this.location=location;
    }
    /**
     * Where the chosen colour should be placed.
     * @return the location of this move.
     */
    public String getColour(){
        return this.colour;
    }
    /**
     * Which colour should be placed on the chosen location.
     * @return the colour of this move
     */
    public int getLocation(){
        return this.location;
    }
}
