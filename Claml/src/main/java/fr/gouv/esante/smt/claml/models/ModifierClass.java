//
// This file was generated by the JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v2.3.1-b171012.0423 
//         See <a href="https://javaee.github.io/jaxb-v2/">https://javaee.github.io/jaxb-v2/</a> 
//         Any modifications to this file will be lost upon recompilation of the source schema. 
//         Generated on: 2018.04.13 at 05:46:14 PM AEST 
//


package fr.gouv.esante.smt.claml.models;

import java.util.ArrayList;
import java.util.List;
import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlIDREF;
import javax.xml.bind.annotation.XmlRootElement;
import javax.xml.bind.annotation.XmlSchemaType;
import javax.xml.bind.annotation.XmlType;
import javax.xml.bind.annotation.adapters.CollapsedStringAdapter;
import javax.xml.bind.annotation.adapters.XmlJavaTypeAdapter;


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
 *         &lt;element ref="{}Meta" maxOccurs="unbounded" minOccurs="0"/&gt;
 *         &lt;element ref="{}SuperClass"/&gt;
 *         &lt;element ref="{}SubClass" maxOccurs="unbounded" minOccurs="0"/&gt;
 *         &lt;element ref="{}Rubric" maxOccurs="unbounded" minOccurs="0"/&gt;
 *         &lt;element ref="{}History" maxOccurs="unbounded" minOccurs="0"/&gt;
 *       &lt;/sequence&gt;
 *       &lt;attribute name="modifier" use="required" type="{http://www.w3.org/2001/XMLSchema}NMTOKEN" /&gt;
 *       &lt;attribute name="code" use="required" type="{http://www.w3.org/2001/XMLSchema}NMTOKEN" /&gt;
 *       &lt;attribute name="usage" type="{http://www.w3.org/2001/XMLSchema}IDREF" /&gt;
 *       &lt;attribute name="variants" type="{http://www.w3.org/2001/XMLSchema}IDREFS" /&gt;
 *     &lt;/restriction&gt;
 *   &lt;/complexContent&gt;
 * &lt;/complexType&gt;
 * </pre>
 * 
 * 
 */
@XmlAccessorType(XmlAccessType.FIELD)
@XmlType(name = "", propOrder = {
    "meta",
    "superClass",
    "subClass",
    "rubric",
    "history"
})
@XmlRootElement(name = "ModifierClass")
public class ModifierClass {

    @XmlElement(name = "Meta")
    protected List<Meta> meta;
    @XmlElement(name = "SuperClass", required = true)
    protected SuperClass superClass;
    @XmlElement(name = "SubClass")
    protected List<SubClass> subClass;
    @XmlElement(name = "Rubric")
    protected List<Rubric> rubric;
    @XmlElement(name = "History")
    protected List<History> history;
    @XmlAttribute(name = "modifier", required = true)
    @XmlJavaTypeAdapter(CollapsedStringAdapter.class)
    @XmlSchemaType(name = "NMTOKEN")
    protected String modifier;
    @XmlAttribute(name = "code", required = true)
    @XmlJavaTypeAdapter(CollapsedStringAdapter.class)
    @XmlSchemaType(name = "NMTOKEN")
    protected String code;
    @XmlAttribute(name = "usage")
    @XmlIDREF
    @XmlSchemaType(name = "IDREF")
    protected Object usage;
    @XmlAttribute(name = "variants")
    @XmlIDREF
    @XmlSchemaType(name = "IDREFS")
    protected List<Object> variants;

    /**
     * Gets the value of the meta property.
     * 
     * <p>
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the meta property.
     * 
     * <p>
     * For example, to add a new item, do as follows:
     * <pre>
     *    getMeta().add(newItem);
     * </pre>
     * 
     * 
     * <p>
     * Objects of the following type(s) are allowed in the list
     * {@link Meta }
     * 
     * 
     */
    public List<Meta> getMeta() {
        if (meta == null) {
            meta = new ArrayList<Meta>();
        }
        return this.meta;
    }

    /**
     * Gets the value of the superClass property.
     * 
     * @return
     *     possible object is
     *     {@link SuperClass }
     *     
     */
    public SuperClass getSuperClass() {
        return superClass;
    }

    /**
     * Sets the value of the superClass property.
     * 
     * @param value
     *     allowed object is
     *     {@link SuperClass }
     *     
     */
    public void setSuperClass(SuperClass value) {
        this.superClass = value;
    }

    /**
     * Gets the value of the subClass property.
     * 
     * <p>
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the subClass property.
     * 
     * <p>
     * For example, to add a new item, do as follows:
     * <pre>
     *    getSubClass().add(newItem);
     * </pre>
     * 
     * 
     * <p>
     * Objects of the following type(s) are allowed in the list
     * {@link SubClass }
     * 
     * 
     */
    public List<SubClass> getSubClass() {
        if (subClass == null) {
            subClass = new ArrayList<SubClass>();
        }
        return this.subClass;
    }

    /**
     * Gets the value of the rubric property.
     * 
     * <p>
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the rubric property.
     * 
     * <p>
     * For example, to add a new item, do as follows:
     * <pre>
     *    getRubric().add(newItem);
     * </pre>
     * 
     * 
     * <p>
     * Objects of the following type(s) are allowed in the list
     * {@link Rubric }
     * 
     * 
     */
    public List<Rubric> getRubric() {
        if (rubric == null) {
            rubric = new ArrayList<Rubric>();
        }
        return this.rubric;
    }

    /**
     * Gets the value of the history property.
     * 
     * <p>
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the history property.
     * 
     * <p>
     * For example, to add a new item, do as follows:
     * <pre>
     *    getHistory().add(newItem);
     * </pre>
     * 
     * 
     * <p>
     * Objects of the following type(s) are allowed in the list
     * {@link History }
     * 
     * 
     */
    public List<History> getHistory() {
        if (history == null) {
            history = new ArrayList<History>();
        }
        return this.history;
    }

    /**
     * Gets the value of the modifier property.
     * 
     * @return
     *     possible object is
     *     {@link String }
     *     
     */
    public String getModifier() {
        return modifier;
    }

    /**
     * Sets the value of the modifier property.
     * 
     * @param value
     *     allowed object is
     *     {@link String }
     *     
     */
    public void setModifier(String value) {
        this.modifier = value;
    }

    /**
     * Gets the value of the code property.
     * 
     * @return
     *     possible object is
     *     {@link String }
     *     
     */
    public String getCode() {
        return code;
    }

    /**
     * Sets the value of the code property.
     * 
     * @param value
     *     allowed object is
     *     {@link String }
     *     
     */
    public void setCode(String value) {
        this.code = value;
    }

    /**
     * Gets the value of the usage property.
     * 
     * @return
     *     possible object is
     *     {@link Object }
     *     
     */
    public Object getUsage() {
        return usage;
    }

    /**
     * Sets the value of the usage property.
     * 
     * @param value
     *     allowed object is
     *     {@link Object }
     *     
     */
    public void setUsage(Object value) {
        this.usage = value;
    }

    /**
     * Gets the value of the variants property.
     * 
     * <p>
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the variants property.
     * 
     * <p>
     * For example, to add a new item, do as follows:
     * <pre>
     *    getVariants().add(newItem);
     * </pre>
     * 
     * 
     * <p>
     * Objects of the following type(s) are allowed in the list
     * {@link Object }
     * 
     * 
     */
    public List<Object> getVariants() {
        if (variants == null) {
            variants = new ArrayList<Object>();
        }
        return this.variants;
    }

}
