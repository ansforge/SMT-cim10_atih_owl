//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v2.3.1-b171012.0423 
//         See <a href="https://javaee.github.io/jaxb-v2/">https://javaee.github.io/jaxb-v2/</a> 
//         Any modifications to this file will be lost upon recompilation of the source schema. 
//         Generated on: 2018.04.13 at 05:46:14 PM AEST 
//


package fr.gouv.esante.smt.claml.models;

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;
import javax.xml.bind.annotation.XmlType;


/**
 * <p>Java class for anonymous complex type.
 * 
 * <p>The following schema fragment specifies the expected         content contained within this class.
 * 
 * <pre>
 * &lt;complexType&gt;
 *   &lt;complexContent&gt;
 *     &lt;restriction base="{http://www.w3.org/2001/XMLSchema}anyType"&gt;
 *       &lt;sequence&gt;
 *         &lt;element ref="{}Caption" minOccurs="0"/&gt;
 *         &lt;element ref="{}THead" minOccurs="0"/&gt;
 *         &lt;element ref="{}TBody" minOccurs="0"/&gt;
 *         &lt;element ref="{}TFoot" minOccurs="0"/&gt;
 *       &lt;/sequence&gt;
 *       &lt;attribute name="class" type="{http://www.w3.org/2001/XMLSchema}string" /&gt;
 *     &lt;/restriction&gt;
 *   &lt;/complexContent&gt;
 * &lt;/complexType&gt;
 * </pre>
 * 
 * 
 */
@XmlAccessorType(XmlAccessType.FIELD)
@XmlType(name = "", propOrder = {
    "caption",
    "tHead",
    "tBody",
    "tFoot"
})
@XmlRootElement(name = "Table")
public class Table {

    @XmlElement(name = "Caption")
    protected Caption caption;
    @XmlElement(name = "THead")
    protected THead tHead;
    @XmlElement(name = "TBody")
    protected TBody tBody;
    @XmlElement(name = "TFoot")
    protected TFoot tFoot;
    @XmlAttribute(name = "class")
    protected String clazz;

    /**
     * Gets the value of the caption property.
     * 
     * @return
     *     possible object is
     *     {@link Caption }
     *     
     */
    public Caption getCaption() {
        return caption;
    }

    /**
     * Sets the value of the caption property.
     * 
     * @param value
     *     allowed object is
     *     {@link Caption }
     *     
     */
    public void setCaption(Caption value) {
        this.caption = value;
    }

    /**
     * Gets the value of the tHead property.
     * 
     * @return
     *     possible object is
     *     {@link THead }
     *     
     */
    public THead getTHead() {
        return tHead;
    }

    /**
     * Sets the value of the tHead property.
     * 
     * @param value
     *     allowed object is
     *     {@link THead }
     *     
     */
    public void setTHead(THead value) {
        this.tHead = value;
    }

    /**
     * Gets the value of the tBody property.
     * 
     * @return
     *     possible object is
     *     {@link TBody }
     *     
     */
    public TBody getTBody() {
        return tBody;
    }

    /**
     * Sets the value of the tBody property.
     * 
     * @param value
     *     allowed object is
     *     {@link TBody }
     *     
     */
    public void setTBody(TBody value) {
        this.tBody = value;
    }

    /**
     * Gets the value of the tFoot property.
     * 
     * @return
     *     possible object is
     *     {@link TFoot }
     *     
     */
    public TFoot getTFoot() {
        return tFoot;
    }

    /**
     * Sets the value of the tFoot property.
     * 
     * @param value
     *     allowed object is
     *     {@link TFoot }
     *     
     */
    public void setTFoot(TFoot value) {
        this.tFoot = value;
    }

    /**
     * Gets the value of the clazz property.
     * 
     * @return
     *     possible object is
     *     {@link String }
     *     
     */
    public String getClazz() {
        return clazz;
    }

    /**
     * Sets the value of the clazz property.
     * 
     * @param value
     *     allowed object is
     *     {@link String }
     *     
     */
    public void setClazz(String value) {
        this.clazz = value;
    }

}